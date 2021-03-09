/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2016-2020 Philipp Ruemmer <ph_r@gmx.net>
 *               2020      Zafer Esen <zafer.esen@gmail.com>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package ap.theories

import ap.basetypes._
import ap.parser.IExpression.Predicate
import ap.parser._
import ap.types._
import ap.util.Debug

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap, Map => MMap, Set => MSet}
import scala.collection.{mutable, Map => GMap}

object Heap {
  private val AC = Debug.AC_ADT
  abstract sealed class CtorArgSort
  case class ADTSort(num : Int) extends CtorArgSort
  case class OtherSort(sort : Sort) extends CtorArgSort
  case object AddressCtor extends CtorArgSort
  case class CtorSignature(arguments : Seq[(String, CtorArgSort)],
                           result : ADTSort)

  class HeapException(m : String) extends Exception(m)

  class AddressSort(sortName : String,
                    val heapTheory : Heap) extends ProxySort(Sort.Nat) {
    import IExpression.toFunApplier

    override val name = sortName
    override def decodeToTerm(
                 d : IdealInt,
                 assignment : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
      Some(heapTheory.nthAddr(d.intValue))

    override lazy val individuals : Stream[ITerm] =
      for (t <- Sort.Nat.individuals) yield heapTheory.nthAddr(t)
  }

  class HeapSort(sortName : String,
                 val heapTheory : Heap) extends ProxySort(Sort.Integer) {
    import IExpression.toFunApplier
    import ap.terfor.conjunctions.Conjunction
    import ap.terfor.preds.Atom
    import heapTheory.{ObjectSort, alloc, emptyHeap, newHeap}
    override val name = sortName

    override lazy val individuals : Stream[ITerm] =
      emptyHeap() #:: (for (t <- individuals;
                            obj <- ObjectSort.individuals)
        yield newHeap(alloc(t, obj)))

    override def decodeToTerm(
                 d : IdealInt,
                 assignment : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] = {
      assignment get ((d, this))
    }

    override def augmentModelTermSet(
                 model : Conjunction,
                 terms : MMap[(IdealInt, Sort), ITerm],
                 allTerms : Set[(IdealInt, Sort)],
                 definedTerms : MSet[(IdealInt, Sort)]) : Unit = {

      /** Helper function to collect atoms from theory functions */
      def getAtoms (f : IFunction) : IndexedSeq[Atom] =
        model.predConj positiveLitsWithPred heapTheory.heapFunPredMap(f)

      /* Collect the relevant functions and predicates of the theory */
      import heapTheory.{counter, emptyHeap, read, write, allocHeap}
      val writeAtoms = getAtoms(write)
      val allocAtoms = getAtoms(allocHeap)
      val readAtoms = getAtoms(read)
      val counterAtoms = getAtoms(counter)
      val emptyHeapAtoms = getAtoms(emptyHeap)

      import IExpression.{i, toFunApplier}

      def createHeapTerm(contents : Seq[IdealInt]) : ITerm = {
        assume(contents.nonEmpty) // emptyHeap should be handled separately
        import heapTheory.{_defObj, alloc, newHeap}
        var currentTerm = emptyHeap()
        for (objTermId <- contents) {
          val objTerm = terms.getOrElse((objTermId, heapTheory.ObjectSort),
            heapTheory._defObj)
          currentTerm = newHeap(alloc(currentTerm, objTerm))
        }
        currentTerm
      }

      val heapContents = new MHashMap[IdealInt, ArrayBuffer[IdealInt]] //[eh->[],h1:[1,2],...]

      // fill in the contents for empty heaps
      for (a <- emptyHeapAtoms) { // emptyHeap(heapId)
          heapContents += ((a(0).constant, new ArrayBuffer[IdealInt](0)))
      }
      // initialize content buffers of non-empty heaps
      // counter(heapId, counterVal)
      for (a <- counterAtoms if a(1).constant.intValue > 0) {
        val heapId = a(0).constant
        val counterVal = a(1).constant
        val contentBuffer = new ArrayBuffer[IdealInt](counterVal.intValue)
        for (_ <- 0 until counterVal.intValue)
          contentBuffer += -1
        heapContents += ((heapId,contentBuffer))
      }

      var somethingChanged = true
      // iterate over non-empty heaps to fixed-point
      while(somethingChanged) {
        somethingChanged = false
        for (a <- counterAtoms if a(1).constant.intValue > 0) {
          val heapId = a(0).constant
          val counterVal = a(1).constant
          /*
        * A heap is either created through an alloc, or through a write.
        * If it is created through alloc, all locations except the last location
        * (i.e., counterVal), are the same as the original heap.
        * If it is created through write, all locations except the written
        * location, are the same as the original heap.
        */
          // allocHeap(prevHeapId, obj, heapId)
          val (prevHeapId, changedAddr, newObj, allocOrWriteFound) = allocAtoms
            .find(p => p(2).constant == heapId) match {
            case Some(p) => (p(0).constant, counterVal, p(1).constant, true)
            case None => // no allocs found, then there must be a write
              // write(prevHeapId, addr, obj, heapId)
              writeAtoms.find(p => p(3).constant == heapId) match {
                case Some(p) => (p(0).constant, p(1).constant, p(2).constant, true)
                case None => // no writes nor allocs found
                  (IdealInt(-1), IdealInt(-1), IdealInt(-1), false)
              }
          }

          if (prevHeapId != heapId) {
            if (allocOrWriteFound) {
              // copy all locations from previous heap, then update changed loc
              val changedInd = changedAddr.intValue - 1
              val thisHeap = heapContents(heapId)
              if (counterVal.intValue > 1) { // otherwise prevHeap is the empty heap
                val prevHeap = heapContents(prevHeapId)
                for (i <- prevHeap.indices if i != changedInd) {
                  if (thisHeap(i) != prevHeap(i)) somethingChanged = true
                  thisHeap(i) = prevHeap(i)
                }
              }
              thisHeap(changedInd) = newObj // this does not depend on prev heaps.
            } else { // try to find the contents through read atoms
              for (a <- readAtoms if a(0).constant == heapId) {
                val changedInd = a(1).constant.intValue - 1
                val newVal = a(2).constant
                if (heapContents(heapId)(changedInd) != newVal) {
                  heapContents(heapId)(changedInd) = newVal
                  somethingChanged = true
                }
              }
            }
          }
        }
      }

      // define emptyHeap terms
      for (a <- emptyHeapAtoms) {
        val heapKey = (a(0).constant, this)
        if (!(definedTerms contains heapKey)) {
          terms.put(heapKey, emptyHeap())
          definedTerms += heapKey
        }
      }

      // define rest of the heap terms
      for (a <- counterAtoms if a(1).constant.intValue > 0) {
        val heapId = a(0).constant
        val heapKey = (heapId, this)
        val heapTerm = createHeapTerm(heapContents(heapId))
        if (!(definedTerms contains heapKey) || //if this term is not defined
            (terms(heapKey) != heapTerm)) { // or has changed
          terms.put(heapKey, heapTerm) //update the heap term
          if (!(definedTerms contains heapKey)) definedTerms += heapKey
        }
      }
    }
  }

  /**
   * Extractor recognising the functions of any Heap theory.
   */
  object HeapFunExtractor {
    def unapply(fun : IFunction) : Option[Heap] =
      (TheoryRegistry lookupSymbol fun) match {
        case Some(t : Heap) => Some(t)
        case _ => None
      }
  }

  /**
   * Extractor recognising the predicates of any Heap theory.
   */
  object HeapPredExtractor {
    def unapply(pred : Predicate) : Option[Heap] =
      (TheoryRegistry lookupSymbol pred) match {
        case Some(t : Heap) => Some(t)
        case _ => None
      }
  }
}

/**
 * @param heapSortName
 * @param addressSortName
 * @param objectSort
 * @param sortNames
 * @param ctorSignatures
 */
class Heap(heapSortName : String, addressSortName : String,
           objectSort : Heap.ADTSort, sortNames : Seq[String], // todo: fix objectSort not used
           ctorSignatures : Seq[(String, Heap.CtorSignature)],
           defaultObjectCtor : (ADT, ADT) => ITerm)
    extends Theory {
  import Heap._
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(AC,
    ctorSignatures forall {
      case (_, sig) =>
        ((sig.arguments map (_._2)) ++ List(sig.result)) forall {
          case Heap.ADTSort(id) => id >= 0 && id < sortNames.size
          case _ : OtherSort => true
          case Heap.AddressCtor => true
        }
    })
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
  val AddressSort = new AddressSort(addressSortName, this)
  val HeapSort = new HeapSort(heapSortName, this)
  val emptyHeap = new MonoSortedIFunction("empty" + heapSortName,
    argSorts = List(),
    resSort = HeapSort, _partial = false, _relational = false)

  val nthAddr = new MonoSortedIFunction("nth" + addressSortName,
    List(Sort.Nat), AddressSort,
    false, false) // todo: make private?

  /** implicit converters from Heap.CtorArgSort to ADT.CtorArgSort */
  private implicit def HeapSortToADTSort(s : CtorArgSort) : ADT.CtorArgSort =
    s match {
      case t : ADTSort => ADT.ADTSort(t.num)
      case t : OtherSort => ADT.OtherSort(t.sort)
      case AddressCtor => ADT.OtherSort(AddressSort)
    }

  private implicit def HeapSortToADTSort(l : Seq[(String, Heap.CtorSignature)]):
  Seq[(String, ADT.CtorSignature)] = {
    for (s <- l) yield (s._1, ADT.CtorSignature(
      for (arg <- s._2.arguments) yield (arg._1, HeapSortToADTSort(arg._2)),
      ADT.ADTSort(s._2.result.num)))
  }

  val ObjectADT = new ADT(sortNames, ctorSignatures)
  val ObjectSort = ObjectADT.sorts.head

  /** Create return sort of alloc as an ADT: Heap x Address */
  private val AllocResCtorSignature = ADT.CtorSignature(
    List(("new" + heapSortName, ADT.OtherSort(HeapSort)),
      ("new" + addressSortName, ADT.OtherSort(AddressSort))), ADT.ADTSort(0))

  val AllocResADT = new ADT(List("AllocRes" + heapSortName),
    List(("AllocRes" + heapSortName, AllocResCtorSignature)))
  val AllocResSort = AllocResADT.sorts.head
  val newHeap = AllocResADT.selectors(0)(0)
  val newAddr = AllocResADT.selectors(0)(1)

  /** Helper predicate to learn if the argument ADT sort is declared as part of
   * this theory. */
  def containsADTSort(adt : ADT) = adt == ObjectADT || adt == AllocResADT

  /** Functions and predicates of the theory
   * Assuming Address as address sort name, Heap as heap sort name, and
   * Obj as the selected object sort.
   * Some function / predicate names incorporate the defined / selected names.
   * ***************************************************************************
   * Public functions and predicates
   * ***************************************************************************
   * emptyHeap            : ()                   --> Heap
   * alloc                : Heap x Obj           --> Heap x Address (allocResHeap)
   * read                 : Heap x Address       --> Obj
   * write                : Heap x Address x Obj --> Heap
   * valid (isAlloc)      : Heap x Address       --> Bool
   * deAlloc              : Heap                 --> Heap
   * nthAddress           : Nat                  --> Address
   *
   *             0     1
   * writeADT : Obj x Obj --> Heap
   * * Updates the ADT's field (described by a read to 0) using value (1)
   * ***************************************************************************
   * Private functions and predicates
   * ***************************************************************************
   * counter  : Heap                 --> Nat
   *
   * * Below two functions are shorthand functions to get rid of allocRes ADT.
   * * They return a single value instead of the pair <Heap x Addr>.
   * * This is done to get rid of quantifiers related to the ADT in the
   * * generated interpolants.
   * alloc<heapSortName>    : Heap x Obj           --> Heap
   * alloc<addressSortName> : Heap x Obj           --> Address
   *
   * * allocAddress is further removed by reducing it to counter(h) + 1
   * ***************************************************************************
   * */
  val alloc = new MonoSortedIFunction("alloc", List(HeapSort, ObjectSort),
    AllocResSort, false, false)
  val allocHeap = new MonoSortedIFunction("alloc" + heapSortName,
    List(HeapSort, ObjectSort), HeapSort, false, false)
  val deAlloc = new MonoSortedIFunction("deAlloc", List(HeapSort),
    HeapSort, false, false)

  val read = new MonoSortedIFunction("read", List(HeapSort, AddressSort),
    ObjectSort, false, false)
  val write = new MonoSortedIFunction("write",
    List(HeapSort, AddressSort, ObjectSort), HeapSort, false, false)
  val isAlloc = new MonoSortedPredicate("valid", List(HeapSort, AddressSort))
  val nullAddr = new MonoSortedIFunction("null" + addressSortName,
    List(), AddressSort, false, false)

  /**
   * Helper function to write to ADT fields.
   * @param lhs : the ADT field term to be written to. This should be an IFunApp,
   *            where the outermost function is a selector of the ADT, the
   *            innermost function is a heap read to the ADT on the heap, the
   *            innermost+1 function is the getter of the ADT, and any
   *            intermediate functions are other selectors
   *            e.g. x(getS(read(h, p))) or  (in C: p->x)
   *                 x(s(getS(read(h, p))))  (in C: p->s.x)
   *            note that this method works for writing to non-ADTs as well,
   *            if lhs is provided as a read Object (e.g. getInt(read(h,p))).
   * @param rhs : the new value for the field, e.g. 42
   * this would return a new term, such as: S(42, y(s))
   * @return    : the new ADT term
   */
  def writeADT (lhs : IFunApp, rhs : ITerm) : ITerm = {
    import IExpression.toFunApplier
    def updateADT(adtStack : List[ADTFieldPath], parentTerm : ITerm,
                  newVal : ITerm) : ITerm = {
      adtStack match {
        case Nil => // last level
          newVal
        case parent :: tl => import IExpression.toFunApplier
          val newTerm = updateADT(tl, parentTerm, newVal)
          val args = for (i <- parent.sels.indices) yield {
            if (i == parent.updatedSelInd) newTerm
            else parent.sels(i)(parentTerm)
          }
          parent.ctor(args : _*)
      }
    }

    val (adtStack, rootTerm) = generateADTUpdateStack(lhs)
    val newTerm = updateADT(adtStack, rootTerm, rhs)
    rootTerm match {
      case IFunApp(f, args) =>
        f match {
          case sortedF: MonoSortedIFunction // Object read (read(h, p))
            if sortedF.resSort == ObjectSort =>
            write(args(0), args(1), newTerm)
          case sortedF: MonoSortedIFunction // getter read (getInt(read(h, p)))
            if ObjectADT.selectors.exists(s => s contains sortedF) =>
            val readArgs = args.head.asInstanceOf[IFunApp].args
            val wrapper: MonoSortedIFunction =
              ObjectADT.constructors.find(f => f.argSorts.size == 1 &&
                f.argSorts.head == Sort.sortOf(rootTerm)) match {
                case None => throw new HeapException(
                  "Could not find a wrapper for " + rootTerm)
                case Some(f) => f
              }
            write(readArgs(0), readArgs(1), wrapper(newTerm))
          case _ => throw new HeapException("Could not determine write from " +
            "the lhs: " + lhs)
        }
      case _ => throw new HeapException("Could not determine write from " +
        "the lhs: " + lhs)
    }
  }

  private case class ADTFieldPath (ctor : MonoSortedIFunction,
                                sels : Seq[MonoSortedIFunction],
                                updatedSelInd : Int)
  private def generateADTUpdateStack (termPointingToADTField : IFunApp)
  : (List[ADTFieldPath], ITerm) = {
    val ADTUpdateStack = new mutable.Stack[ADTFieldPath]

    def fillParentStack (fieldTerm : IFunApp) : ITerm = {
      assert(fieldTerm.args.size == 1 || fieldTerm.fun == read)
      fieldTerm.args.head match {
        case nested : IFunApp if ObjectADT.constructors.exists(c =>
          c.resSort == nested.fun.asInstanceOf[MonoSortedIFunction].resSort) &&
          nested.fun != read =>

          // here two possibilities:
          // one is that the last level resSort is a getter
          //   (e.g. getS that has the same resSort as a ctor)
          // second is that the last level is simply the ctor
          val ctorInd =
            if(ObjectADT.constructors contains nested.fun) { // first case
              ObjectADT.constructors indexOf nested.fun
            } else { // second case
              ObjectADT.constructors.indexWhere(c =>
                c.resSort == nested.fun.asInstanceOf[MonoSortedIFunction].resSort)
            }

          val sels = ObjectADT.selectors(ctorInd)
          val thisSelInd =
            ObjectADT.selectors(ctorInd).indexWhere(s => s == fieldTerm.fun)
          ADTUpdateStack.push(
            ADTFieldPath(ObjectADT.constructors(ctorInd), sels, thisSelInd))
          // then move on to nested parents
          fillParentStack(nested)
        case _ => fieldTerm
      }
    }
    val rootTerm = fillParentStack (termPointingToADTField)
    (ADTUpdateStack.toList, rootTerm)
  }

  val counter = new MonoSortedIFunction("counter" + addressSortName,
    List(HeapSort), Sort.Nat, false, false)

  val functions = List(emptyHeap, alloc, allocHeap, /*allocAddr,*/ read, write,
                       nullAddr,
                       counter, nthAddr)
  val predefPredicates = List(isAlloc)

  val _defObj : ITerm = defaultObjectCtor(ObjectADT, AllocResADT)
  private def _isAlloc(h: ITerm , p: ITerm) : IFormula = {
    import IExpression._
    counter(h) >= p & p > 0
  }

  val triggeredAxioms : IFormula = {
    import IExpression._
    (
      //row - same (row-upward unit test fails, tested program immediately returns unsat / enters a loop)
      /*HeapSort.all(h => AddressSort.all(p => ObjectSort.all(
        o => trig(_isAlloc(h, p) ==> (read(write(h, p, o), p) === o),
        read(write(h, p, o), p))))) &*/

      // same as above but simpler trigger, unit tests pass, test program ends with "cannot handle general quantifiers..." error)
      HeapSort.all(h => AddressSort.all(p => ObjectSort.all(
        o => trig(_isAlloc(h, p) ==> (read(write(h, p, o), p) === o),
          write(h, p, o))))) &

        // row - same (alternative - HeapTests2 - 1.5 does not terminate, row-upward fails)
        //HeapSort.all(h1 => HeapSort.all(h2 => AddressSort.all(p => ObjectSort.all(
        //  o => trig(_isAlloc(h1, p) & write(h1, p, o) === h2 ==> (read(h2, p) === o),
        //    write(h1, p, o), read(h2, p)))))) &

        // row - same (alternative 2 - unit tests pass, messy interpolants)
        //HeapSort.all(h1 => AddressSort.all(p => ObjectSort.all(
        //  o => trig(_isAlloc(h1, p) ==>
        //    HeapSort.ex(h2 => write(h1, p, o) === h2 & (read(h2, p) === o)),
        //    write(h1, p, o))))) &

        // row - different - downward
        //HeapSort.all(h => AddressSort.all(p1 => ObjectSort.all(o => AddressSort.all(
        //  p2 => trig(p1 =/= p2 ==> (read(write(h, p1, o), p2) === read(h, p2)),
        //    read(write(h, p1, o), p2)))))) &

        // row - different - downward & upward (some tests fail, including ROW-upward)
        //HeapSort.all(h => AddressSort.all(p1 => ObjectSort.all(o => AddressSort.all(
        //  p2 => trig(p1 =/= p2 ==> (read(write(h, p1, o), p2) === read(h, p2)),
        //    read(write(h, p1, o), p2), read(h, p2)))))) &

        //
        //HeapSort.all(h => HeapSort.all(h2 => AddressSort.all(p1 => ObjectSort.all(o => AddressSort.all(
        //  p2 => trig(p1 =/= p2 & write(h, p1, o) === h2 ==> (read(h2, p2) === read(h, p2)),
        //    write(h, p1, o), read(h2, p2))))))) &

        // row - downward
        HeapSort.all(h => AddressSort.all(p1 => ObjectSort.all(o => AddressSort.all(
          p2 => trig(p1 =/= p2 ==> (read(write(h, p1, o), p2) === read(h, p2)),
            write(h, p1, o), read(write(h, p1, o), p2)))))) &

        // row - upward
        HeapSort.all(h => AddressSort.all(p1 => ObjectSort.all(o => AddressSort.all(
          p2 => trig(p1 =/= p2 ==> (read(write(h, p1, o), p2) === read(h, p2)),
            write(h, p1, o), read(h, p2)))))) &

        // same as above, but adding it this way messes everything up, some tests return "inconclusive".
        //HeapSort.all(h => HeapSort.all(h2 => AddressSort.all(p1 => ObjectSort.all(o => AddressSort.all(
        //  p2 => trig(p1 =/= p2 & write(h, p1, o) === h2 ==> (read(h2, p2) === read(h, p2)),
        //    write(h, p1, o), read(h, p2))))))) &

        // invalid write - 1
        HeapSort.all(h => AddressSort.all(p => ObjectSort.all(
          o => trig(counter(h) < p ==> (write(h, p, o) === h), write(h, p, o))))) &
        // invalid write - 2
        HeapSort.all(h => AddressSort.all(p => ObjectSort.all(
          o => trig(p <= 0 ==> (write(h, p, o) === h), write(h, p, o))))) &

        // counter is same after write
        HeapSort.all(h => AddressSort.all(p => ObjectSort.all(
          o => trig(counter(write(h, p, o)) === counter(h), write(h, p, o))))) &

        // invalid read - 1
        HeapSort.all(h => AddressSort.all(p => trig(
          counter(h) < p ==> containFunctionApplications(read(h, p) === _defObj),
          read(h, p)))) &
        // invalid read - 2
        HeapSort.all(h => AddressSort.all(p => trig(
          p <= 0 ==> containFunctionApplications(read(h, p) === _defObj),
          read(h, p)))) &

        /*HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
          (p === counter(h)+1) ==>
          (read(allocHeap(h, o), p) === o ),
            read(allocHeap(h, o), p))))) &

        HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
          (p =/= counter(h)+1) ==>
          (read(allocHeap(h, o), p) === read(h, p)),
            read(allocHeap(h, o), p))))))*/
        HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
          (p === counter(h)+1) ==>
            (read(allocHeap(h, o), p) === o ),
          read(allocHeap(h, o), p), allocHeap(h, o))))) &

        HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
          (p =/= counter(h)+1) ==>
            (read(allocHeap(h, o), p) === read(h, p)),
          read(allocHeap(h, o), p), allocHeap(h, o))))))
    // roa - downward
    //HeapSort.all(h => HeapSort.all(h2 => AddressSort.all(p => ObjectSort.all(o => trig(
    //    (p === counter(h)+1 & allocHeap(h, o) === h2) ==>
    //      (read(h2, p) === o),
    //      allocHeap(h, o), read(h2, p)))))) &

    // roa - upward
    //HeapSort.all(h => HeapSort.all(h2 => AddressSort.all(p => ObjectSort.all(o => trig(
    //    (p =/= counter(h)+1 & allocHeap(h, o) === h2) ==>
    //      (read(h2, p) === read(h, p)),
    //    allocHeap(h, o), read(h2, p), read(h, p)))))))
  }

  val inductionAxioms : IFormula = {
    import IExpression._
    (
    HeapSort.all(h => trig(counter(h) >= 0, counter(h))) & // todo: why removing this fails some test cases? counter resType is Nat.

    HeapSort.all(h => ObjectSort.all(o => trig(
      counter(allocHeap(h, o)) === counter(h) + 1,
      allocHeap(h, o))))
    )
  }

  val theoryAxioms = triggeredAxioms & inductionAxioms

  val (funPredicates, axioms1, order, functionTranslation) = Theory.genAxioms(
    theoryFunctions = functions, theoryAxioms = theoryAxioms,
    otherTheories = List(ObjectADT, AllocResADT))

  val predicates = predefPredicates ++ funPredicates
  val functionPredicateMapping = functions zip funPredicates
  import IExpression.Predicate
  private val heapFunPredMap = new MHashMap[IFunction, Predicate]
  functionPredicateMapping.map(m => heapFunPredMap.put(m._1, m._2))

  import ap.terfor.TerForConvenience._
  import ap.terfor.conjunctions.Conjunction
  import ap.terfor.preds.Atom
  import ap.terfor.{Formula, TermOrder}
  val axioms2 : Formula = {
    implicit val o : TermOrder = order
    forall(Atom(heapFunPredMap(emptyHeap), List(l(v(0))), order) ==>
           Atom(heapFunPredMap(counter), List(l(v(0)), l(0)), order))
  }

  val axioms = Conjunction.conj(List(axioms1, axioms2), order)

  /**
   * Information which of the predicates satisfy the functionality axiom;
   * at some internal points, such predicates can be handled more efficiently
   */
  val functionalPredicates : Set[Predicate] = funPredicates.toSet // todo
  /**
   * Information how interpreted predicates should be handled for
   * e-matching.
   */
  import ap.Signature
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map() // todo
  /**
   * A list of functions that should be considered in automatic trigger
   * generation
   */
  val triggerRelevantFunctions : Set[IFunction] = functions.toSet
  /**
   * Additional axioms that are included if the option
   * <code>+genTotalityAxioms</code> is given to Princess.
   */
  val totalityAxioms : Conjunction = Conjunction.TRUE // todo
  /**
   * Optionally, a plug-in implementing reasoning in this theory
   */
  import ap.proof.goal.Goal
  import ap.proof.theoryPlugins.Plugin
  def plugin: Option[Plugin] = Some(new Plugin {
      def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] =
        None

      override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
        import goal.facts.arithConj.negativeEqs
        import goal.facts.predConj.positiveLitsWithPred
        val counterLits = positiveLitsWithPred(heapFunPredMap(counter))

        //println(goal.facts + "\n")
        import ap.terfor.TerForConvenience._
        import ap.terfor.linearcombination.{LinearCombination => LC}
        import ap.terfor.Term
        import scala.collection.mutable.ArrayBuffer
        val neqTermArr = /* (neq, (h1, h2, c1, c2)) */
          new ArrayBuffer[(LC, (Term, Term, LC, LC))]
        for (neq <- negativeEqs) {
          val (lhs : Term, rhs : Term) = (neq(0)._2, neq(1)._2)
          val (lhsCounterInd, rhsCounterInd) =
            (counterLits.indexWhere(a => a.head.head._2 == lhs),
             counterLits.indexWhere(a => a.head.head._2 == rhs))

          if(lhsCounterInd >= 0 && rhsCounterInd >= 0){
            //println(Console.GREEN_B + "Both counter literals found for " + lhs + " and " + rhs  + Console.RESET)
            val lhsCounterTerm : LC = counterLits(lhsCounterInd).last
            val rhsCounterTerm : LC = counterLits(rhsCounterInd).last
            neqTermArr += ((neq, (lhs, rhs, lhsCounterTerm, rhsCounterTerm)))
          }
          /*else if (lhsCounterInd + rhsCounterInd > -2) /* at least one found*/
          {
            println(Console.YELLOW_B + "Only one counter literal found for " + lhs + " and " + rhs + Console.RESET)
          } else println(Console.RED_B + "No counter literals found for " + lhs + " nor " + rhs  + Console.RESET)*/
        }

        implicit val to = goal.order
        val (neqsToRemove, neqsToAdd) =
          (for ((neq, (h1, h2, c1, c2)) <- neqTermArr) yield {
            import ap.terfor.TerForConvenience.{l, v}
            val readPred : Predicate = heapFunPredMap(read)
            val neqToAdd : Formula =  disjFor(c1 =/= c2,
                exists(exists(exists(
                c1 >= v(2) & v(2) > 0 & // isAlloc(h1, v(2))
                Atom(readPred, List(l(h1), l(v(2)), l(v(1))), goal.order) &
                Atom(readPred, List(l(h2), l(v(2)), l(v(0))), goal.order) &
                l(v(0)) =/= l(v(1))
              ))))
            (neq, neqToAdd)}).unzip

        if (neqsToRemove.isEmpty) {
          List()
        } else {
          List(
            Plugin.RemoveFacts(
              ap.terfor.equations.NegEquationConj(neqsToRemove, goal.order)),
            Plugin.AddAxiom(List(), conj(neqsToAdd), Heap.this)
          )
        }
      }
    })

  /**
   * Optionally, other theories that this theory depends on.
   */
  override val dependencies : Iterable[Theory] = List(ObjectADT, AllocResADT)

  /**
   * Optionally, a pre-processor that is applied to formulas over this
   * theory, prior to sending the formula to a prover. This method
   * will be applied very early in the translation process.
   */
  override def iPreprocess(f : IFormula,
                           signature : Signature) : (IFormula, Signature) =
    (Preproc.visit(f, ()).asInstanceOf[IFormula], signature)

  private def isFunAndMatches (e : IExpression, f : IFunction) : Boolean = {
    e match {
      case IFunApp(`f`, _) => true
      case _ => false
    }
  }
  private object Preproc extends CollectingVisitor[Unit, IExpression] {
    import IExpression._
    def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[IExpression]) : IExpression = t match {
      case IAtom(`isAlloc`, _) if subres(1) == i(0) =>
        //println("Simplified " + t + " to false")
        false
      case IAtom(`isAlloc`, _) =>
        //println("Simplified " + t + " to " + _isAlloc(subres(0).asInstanceOf[ITerm], subres(1).asInstanceOf[ITerm]))
        _isAlloc(subres(0).asInstanceOf[ITerm], subres(1).asInstanceOf[ITerm])
      case IFunApp(`nullAddr`, _) =>  i(0)
      case IFunApp(`nthAddr`, _) => subres.head
      case IFunApp(`write`, _) if subres(1) == i(0) =>
        //println("Simplified " + t + " to " + subres(0))
        subres(0)
      case IFunApp(`write`, _) if isFunAndMatches(subres(0), emptyHeap) =>
        //println("Simplified " + t + " to " + emptyHeap())
        emptyHeap()
      /*case IFunApp(`read`, _) if subres(1) == i(0) =>
        println("Simplified " + t + " to " + _defObj)
        _defObj
      case IFunApp(`read`, _) if isFunAndMatches(subres(0), emptyHeap) =>
        println("Simplified " + t + " to " + _defObj)
        _defObj*/
      case IFunApp(`counter`, _) if isFunAndMatches(subres(0), emptyHeap) =>
        //println("Simplified " + t + " to " + 0)
        i(0)
      case IFunApp(`newHeap`, _) if isFunAndMatches(subres(0), alloc) =>
        val Seq(h, o) = subres(0).asInstanceOf[IFunApp].args
        //println("Simplified " + t + " to " + allocHeap(h, o))
        allocHeap(h, o)
      case IFunApp(`newAddr`, _) if isFunAndMatches(subres(0), alloc) =>
        val Seq(h, _) = subres(0).asInstanceOf[IFunApp].args
        //println("Simplified " + t + " to " + counter(h) + 1)
        counter(h) + 1
      case IFunApp(`alloc`, _) =>
        val h = subres(0).asInstanceOf[ITerm]
        val o = subres(1).asInstanceOf[ITerm]
        //println("Simplified " + t + " to " + AllocResADT.constructors.head(allocHeap(h, o), counter(h)+1))
        AllocResADT.constructors.head(allocHeap(h, o), counter(h)+1)
      /*case IFunApp(`allocHeap`, _) =>
        val h = subres(0).asInstanceOf[ITerm]
        val o = subres(1).asInstanceOf[ITerm]
        HeapSort.eps(h2 => h2 === shiftVars(allocHeap(h, o), 1) &
                           counter(h2) === shiftVars(counter(h) + 1, 1))*/
      case IFunApp(`deAlloc`, _) =>
        val h1 = subres(0).asInstanceOf[ITerm]
        val newt = HeapSort.eps(h2 => ObjectSort.ex(o =>
          shiftVars(h1, 2) === allocHeap(h2, shiftVars(o,2))))
        //println("Simplified " + t + " to " + newt)
        newt
      case t =>
        /*println(Console.YELLOW_B + t + Console.GREEN_B + " " +
                t.getClass + Console.RESET)
        println(Console.BLUE_B + subres + Console.RESET)*/
        t update subres
    }
  }
  /**
   * Optionally, a pre-processor that is applied to formulas over this
   * theory, prior to sending the formula to a prover.
   */

  /*override def preprocess(f : Conjunction,
                          order : TermOrder) : Conjunction = {
    println
    println("Preprocessing:")
    println(f) //println(Console.YELLOW_B + f.quans + Console.RESET)
    val reducerSettings = Param.FUNCTIONAL_PREDICATES.set(ReducerSettings.DEFAULT,
      functionalPredicates)
    val after = ReduceWithConjunction(Conjunction.TRUE, order, reducerSettings)(
      f)
    println(" -> " + after)
    println
    after
  }*/

  /* def preprocess(f : Conjunction, order : TermOrder) : Conjunction = f // todo
  */
  /**
   * Optionally, a plugin for the reducer applied to formulas both before
   * and during proving.
   */
  // val reducerPlugin : ReducerPluginFactory = IdentityReducerPluginFactory // todo
  /**
   * Optionally, a function evaluating theory functions applied to concrete
   * arguments, represented as constructor terms.
   */
  // def evalFun(f : IFunApp) : Option[ITerm] = None // todo
  /**
   * Optionally, a function evaluating theory predicates applied to concrete
   * arguments, represented as constructor terms.
   */
  // def evalPred(p : IAtom) : Option[Boolean] = None // todo
  /**
   * If this theory defines any <code>Theory.Decoder</code>, which
   * can translate model data into some theory-specific representation,
   * this function can be overridden to pre-compute required data
   * from a model.
   */
  /* def generateDecoderData(model : Conjunction)
  : Option[Theory.TheoryDecoderData] =
    None */
  // todo
  /**
   * Check whether we can tell that the given combination of theories is
   * sound for checking satisfiability of a problem, i.e., if proof construction
   * ends up in a dead end, can it be concluded that a problem is satisfiable.
   */
  override def isSoundForSat( // todo
                  theories : Seq[Theory],
                  config : Theory.SatSoundnessConfig.Value) : Boolean =
    config match {
      case Theory.SatSoundnessConfig.Elementary  => true
      case Theory.SatSoundnessConfig.Existential => true
      case _                                     => false
    }

  override val postSimplifiers : Seq[IExpression => IExpression] = Vector(rewriter)

  TheoryRegistry register this
  override def toString = "HeapTheory"

  import IBinJunctor._
  import IIntRelation._
  import IExpression._
  import Quantifier._

  def rewriter(expr : IExpression) : IExpression = expr match {
    // add other cases
    case f@IQuantified(EX, subf) =>
      if (f.asInstanceOf[IQuantified].sort == HeapSort) {
        val h1 = ISortedVariable(0, HeapSort)
        subf match {
          case IBinFormula(`And`,
          IEquation(IFunApp(`counter`, Seq(IVariable(0))), n),
          IEquation(IFunApp(`allocHeap`, Seq(IVariable(0), o)), h2)) =>
            val simpf =
              IQuantified(EX, HeapSort, counter(h1) === n &
                h1 === deAlloc(h2) &
                counter(h2) === counter(h1) + 1 &
                read(h2, counter(h2)) === o)
            //println("Simplified: " + f + " to " + simpf)
            simpf
          case _ => expr //println(expr); expr
        }
      }
      else  expr //{println(expr); expr}
    //println("ex:" + expr.asInstanceOf[IQuantified].sort + " " + f); expr
    // simplifies both  forall h: H, !(read(h, _) = o)  and
    //                  forall h: H, read(h, _) = o to false

    case f@IQuantified(ALL, subf) if f.sort == HeapSort &
      (subf match {
        case INot(Eq(IFunApp(`read`, Seq(IVariable(0), _*)), obj))
          if !obj.isInstanceOf[IFunApp] => true
        case INot(Eq(obj, IFunApp(`read`, Seq(IVariable(0), _*))))
          if !obj.isInstanceOf[IFunApp] => true
        case Eq(IFunApp(`read`, Seq(IVariable(0), _*)), obj)
          if !obj.isInstanceOf[IFunApp] => true
        case Eq(obj, IFunApp(`read`, Seq(IVariable(0), _*)))
          if !obj.isInstanceOf[IFunApp] => true
        case _  => false
      }) => //println("simplified: " + f + " to " + "false")
      IBoolLit(false)
    case f@IQuantified(ALL, subf) if f.sort == HeapSort &
      (subf match {
        case INot(Eq(IFunApp(_, Seq(IFunApp(`read`, Seq(IVariable(0), _*)), _*)), _)) =>
          true
        case _ =>
          false
      }) => //println("simplified: " + f + " to " + "true")
      IBoolLit(true)
    case f@IQuantified(ALL, subf) if f.sort == HeapSort &
      (subf match {
        case Eq(IFunApp(`read`, Seq(IVariable(0), _*)), obj)
          if !obj.isInstanceOf[IFunApp] => true
        case Eq(obj, IFunApp(`read`, Seq(IVariable(0), _*)))
          if !obj.isInstanceOf[IFunApp] => true
        case _  => false
      }) => //println("Rewrote: " + f + " to " + "false")
      IBoolLit(false)
    case f@IQuantified(ALL, subf) if f.sort == HeapSort &
      (subf match {
        case INot(Eq(IFunApp(`read`, Seq(IVariable(0), _*)), obj))
          if !obj.isInstanceOf[IFunApp] => true
        case INot(Eq(obj, IFunApp(`read`, Seq(IVariable(0), _*))))
          if !obj.isInstanceOf[IFunApp] => true
        case _  => false
      }) => //println("Rewrote: " + f + " to " + "true")
      IBoolLit(true)
    /*case IQuantified(ALL, f) =>
      println(expr); expr*/
    /*case Eq(IFunApp(`counter`, Seq(h)), IIntLit(IdealInt(0))) =>
      println("Simplified: " + expr + " to " + (h === emptyHeap()))
      h === emptyHeap()*/
    /*case IFunApp(`read`, Seq(_, IIntLit(IdealInt(0)))) =>
      println("Rewrote: " + expr + " to " + _defObj)
      _defObj*/
    /*case Eq(`_defObj`, IFunApp(`read`, Seq(h, p))) =>
      println("Simplified: " + expr + " to " + !_isAlloc(h, p))
      !_isAlloc(h, p) */
    case _ => expr
  }

}
