/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2022-2023 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories.arrays

import ap.Signature
import ap.parser._
import ap.theories._
import ap.types.{Sort, MonoSortedIFunction, MonoSortedPredicate}
import ap.terfor.conjunctions.Conjunction
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin
import ap.terfor.{TermOrder, TerForConvenience, AliasStatus}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.Atom
import ap.util.{Debug, Seqs}

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet,
                                 ArrayBuffer, LinkedHashSet}

object CartArray {

  val AC = Debug.AC_ARRAY


}


/**
 * A theory of Cartesian arrays, with the possibility to project
 * arrays to a subset of their indexes.
 */
class CartArray(val indexSorts         : Seq[Sort],
                val objSort            : Sort,
                val maxProjectionDepth : Int,
                val combinatorSpecs    : IndexedSeq[CombArray.CombinatorSpec],
                val extraDependencies  : Seq[Theory] = List())
   extends Theory {

  import CartArray.AC
  import CombArray.CombinatorSpec

  private val partial = false

  private val (projSorts     : Map[(Seq[Sort], Int), Seq[Sort]],
               allIndexSorts : LinkedHashSet[Seq[Sort]],
               allToSorts    : Seq[Seq[Sort]]) = {
    val projs                = new MHashMap[(Seq[Sort], Int), Seq[Sort]]
    val allSorts, allToSorts = new LinkedHashSet[Seq[Sort]]

    def addProj(sorts : Seq[Sort], depth : Int) : Unit =
      if ((allSorts add sorts) && depth > 0) {
        for (n <- 0 until sorts.size) {
          val newSorts = sorts.patch(n, List(), 1)
          projs.put((sorts, n), newSorts)
          allToSorts add newSorts
          addProj(newSorts, depth - 1)
        }
      }

    addProj(indexSorts, maxProjectionDepth)

    (projs.toMap, allSorts, allToSorts.toVector)
  }

  val extTheories : Map[Seq[Sort], ExtArray] =
    (for (s <- allIndexSorts.iterator) yield {
       s -> new ExtArray(s, objSort)
     }).toMap

  val combTheories : Map[Seq[Sort], CombArray] =
    (for ((s, t) <- extTheories.iterator) yield {
       s -> new CombArray(Vector(t), combinatorSpecs, extraDependencies)
     }).toMap

  val (projections  : Map[(Seq[Sort], Int), IFunction],
       projections2 : Map[(Seq[Sort], Int), IFunction],
       arrayStores  : Map[(Seq[Sort], Int), IFunction],
       arrayStores2 : Map[(Seq[Sort], Int), IFunction],
       functions    : Seq[IFunction]) = {
    val projs, projs2, aStore, aStore2 =
      new MHashMap[(Seq[Sort], Int), IFunction]
    val functions =
      new ArrayBuffer[IFunction]

    for ((key@(fromSorts, ind), toSorts) <- projSorts) {
      val projName1 =
        "proj_" + (
          for ((s, n) <- fromSorts.zipWithIndex)
          yield (if (n == ind) s.name.toUpperCase else s)).mkString("_")
      val projName2 =
        projName1.patch(4, "2", 0)
      val aStoreName1 =
        projName1.patch(0, "arrayStore", 4)
      val aStoreName2 =
        projName2.patch(0, "arrayStore", 4)

      val Seq(proj1, proj2) =
        for (name <- List(projName1, projName2))
        yield MonoSortedIFunction(name,
                                  List(extTheories(fromSorts).sort,
                                       fromSorts(ind)),
                                  extTheories(toSorts).sort,
                                  partial, false)
      val Seq(arrayStore1, arrayStore2) =
        for (name <- List(aStoreName1, aStoreName2))
        yield MonoSortedIFunction(name,
                                  List(extTheories(fromSorts).sort,
                                       fromSorts(ind),
                                       extTheories(toSorts).sort),
                                  extTheories(fromSorts).sort,
                                  partial, false)

      projs  .put(key, proj1)
      projs2 .put(key, proj2)
      aStore .put(key, arrayStore1)
      aStore2.put(key, arrayStore2)
      functions += proj1
      functions += proj2
      functions += arrayStore1
      functions += arrayStore2
    }

    (projs.toMap, projs2.toMap, aStore.toMap, aStore2.toMap, functions.toSeq)
  }

  /**
   * Map index sorts ot the corresponding array sort.
   */
  val arraySorts =
    extTheories mapValues (_.sort)

  /**
   * Polymorphic select.
   */
  def sel(ar : ITerm, indexes : ITerm*) : ITerm = {
    val indexSorts = (Sort sortOf ar) match {
      case ExtArray.ArraySort(theory) =>
        theory.indexSorts
      case _ =>
        throw new Exception(
          "select can only be applied to array terms, not " + ar)
    }
    IFunApp(extTheories(indexSorts).select, List(ar) ++ indexes)
  }

  /**
   * Polymorphic store.
   */
  def sto(ar : ITerm, args : ITerm*) : ITerm = {
    val indexSorts = (Sort sortOf ar) match {
      case ExtArray.ArraySort(theory) =>
        theory.indexSorts
      case _ =>
        throw new Exception(
          "select can only be applied to array terms, not " + ar)
    }
    IFunApp(extTheories(indexSorts).store, List(ar) ++ args)
  }

  /**
   * Polymorphic const.
   */
  def con(indexSorts : Seq[Sort], value : ITerm) : ITerm =
    IFunApp(extTheories(indexSorts).const, List(value))

  /**
   * Project a Cartesian array by assigning some of its indexes to
   * fixed values.
   */
  def proj(ar : ITerm, projectedIndexes : (Int, ITerm)*) : ITerm = {
    val indexes = projectedIndexes sortBy (-_._1)
    var res : ITerm = ar

    for ((ind, value) <- indexes) {
      val indexSorts =
        (Sort sortOf res) match {
          case ExtArray.ArraySort(theory) =>
            theory.indexSorts
          case _ =>
            throw new Exception(
              "Projection can only be applied to array terms, not " + res)
        }
      val projection =
        (projections get (indexSorts, ind)) match {
          case Some(f) =>
            f
          case None =>
            throw new Exception(
              "Projection for index " + ind +
                " not defined for arrays of type " + (Sort sortOf res))
        }
      res = IFunApp(projection, List(res, value))
    }

    res
  }

  /**
   * Update a slice of a Cartesian array.
   */
  def arraySto(ar : ITerm, updatedSlice : ((Int, ITerm), ITerm)) : ITerm = {
    val ((ind, indValue), ar2) = updatedSlice

    val indexSorts =
      (Sort sortOf ar) match {
        case ExtArray.ArraySort(theory) =>
          theory.indexSorts
        case _ =>
          throw new Exception(
            "arrayStore can only be applied to array terms, not " + ar)
      }
    val aStore =
      (arrayStores get (indexSorts, ind)) match {
          case Some(f) =>
            f
          case None =>
            throw new Exception(
              "arrayStore for index " + ind +
                " not defined for arrays of type " + (Sort sortOf ar))
      }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    val toSorts = projSorts((indexSorts, ind))
    Debug.assertPre(AC, (Sort sortOf indValue) == indexSorts(ind),
                    "arrayStore with ill-typed index term")
    Debug.assertPre(AC, (Sort sortOf ar2) == extTheories(toSorts).sort,
                    "arrayStore with ill-typed array slice")
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    IFunApp(aStore, List(ar, indValue, ar2))
  }

  class CombinatorApplicator(n : Int) {
    def apply(arrays : ITerm*) : ITerm = {
      val sorts = arrays map (Sort sortOf _)
      if (sorts.toSet.size != 1)
        throw new Exception(
          "Combinators can only be applied to arrays with consistent sorts, "+
            "not " + (arrays mkString ", "))
      val indexSorts = sorts.head match {
        case ExtArray.ArraySort(theory) =>
          theory.indexSorts
        case _ =>
          throw new Exception(
            "Combinators can only be applied to arrays, not " +
              (arrays mkString ", "))
      }
      IFunApp(combTheories(indexSorts).combinators(n), arrays)
    }
  }

  /**
   * Polymorphic array combinators, corresponding to the
   * <code>combinatorSpecs</code> passed as constructor arguments.
   */
  val combinators : IndexedSeq[CombinatorApplicator] =
    for ((_, n) <- combinatorSpecs.zipWithIndex)
    yield new CombinatorApplicator(n)

  //////////////////////////////////////////////////////////////////////////////

  // Upward propagation for projections, projections2:
  // select(proj_i(ar, indi), ind1, ..., indk) ==
  //   select(ar, ind1, ..., indi, ..., indk)
  //
  // Downward propagation for projections2:
  // proj2_i(ar, indi) == ar2 & select(ar, ind1, ..., indi, ..., indk) = obj
  //   => select(ar2, ind1, ..., indk) == obj
  //
  val axiom1 : IFormula = IExpression.and(
    for ((key@(fromSorts, ind), proj1) <- projections) yield {
      import IExpression._

      val toSorts        = projSorts(key)
      val fromExtTheory  = extTheories(fromSorts)
      val toExtTheory    = extTheories(toSorts)

      val arVar          = v(0, fromExtTheory.sort)
      val indexVars      = for ((s, n) <- fromSorts.toList.zipWithIndex)
                           yield v(n + 1, s)
      val allVars        = arVar :: indexVars
      val varSorts       = for (ISortedVariable(_, s) <- allVars) yield s

      val otherIndexVars = indexVars.patch(ind, List(), 1)

      val sel2Expr       = fromExtTheory.select(arVar :: indexVars : _*)

      val proj2          = projections2(key)

      and(for (proj <- List(proj1, proj2)) yield {
            val projExpr = proj(arVar, indexVars(ind))
            val selExpr  = toExtTheory.select(projExpr :: otherIndexVars : _*)
            val matrix   = ITrigger(List(selExpr), selExpr === sel2Expr)

            val compMatrix =
              if (proj == proj2) {
                ITrigger(List(projExpr, sel2Expr), matrix)
              } else {
                matrix
              }

            all(varSorts, compMatrix)
          })
    })

  // Upward propagation for arrayStore, arrayStore2; and
  // downward propagation for arrayStore2:
  // select(arrayStore_i(ar, indi, ar2), ind1, ..., indk) ==
  //   select(ar2, ind1, ..., indi-1, indi+1, ..., indk)
  //
  val axiom2 : IFormula = IExpression.and(
    for ((key@(fromSorts, ind), aStore1) <- arrayStores) yield {
      import IExpression._

      val toSorts        = projSorts(key)
      val fromExtTheory  = extTheories(fromSorts)
      val toExtTheory    = extTheories(toSorts)

      val arVar          = v(0, fromExtTheory.sort)
      val ar2Var         = v(1, toExtTheory.sort)
      val indexVars      = for ((s, n) <- fromSorts.toList.zipWithIndex)
                           yield v(n + 2, s)
      val allVars        = arVar :: ar2Var :: indexVars
      val varSorts       = for (ISortedVariable(_, s) <- allVars) yield s

      val otherIndexVars = indexVars.patch(ind, List(), 1)

      val sel2Expr       = toExtTheory.select(ar2Var :: otherIndexVars : _*)

      val aStore2        = arrayStores2(key)

      and(for (aStore <- List(aStore1, aStore2)) yield {
            val storeExpr = aStore(arVar, indexVars(ind), ar2Var)
            val selExpr   = fromExtTheory.select(storeExpr :: indexVars : _*)

            val matrix    = ITrigger(List(selExpr), selExpr === sel2Expr)

            val compMatrix =
              if (aStore == aStore2) {
                ITrigger(List(storeExpr, sel2Expr), matrix)
              } else {
                matrix
              }

            all(varSorts, compMatrix)
          })
    })

  // Upward propagation part 2 for arrayStore, arrayStore2; and
  // downward propagation for arrayStore2:
  // indi != ind' =>
  // select(arrayStore_i(ar, indi', ar2), ind1, ..., indk) ==
  //   select(ar, ind1, ..., indk)
  //
  val axiom3 : IFormula = IExpression.and(
    for ((key@(fromSorts, ind), aStore1) <- arrayStores) yield {
      import IExpression._

      val toSorts        = projSorts(key)
      val fromExtTheory  = extTheories(fromSorts)
      val toExtTheory    = extTheories(toSorts)

      val arVar          = v(0, fromExtTheory.sort)
      val ar2Var         = v(1, toExtTheory.sort)
      val indexVar2      = v(2, fromSorts(ind))
      val indexVars      = for ((s, n) <- fromSorts.toList.zipWithIndex)
                           yield v(n + 3, s)
      val allVars        = arVar :: ar2Var :: indexVar2 :: indexVars
      val varSorts       = for (ISortedVariable(_, s) <- allVars) yield s

      val sel2Expr       = fromExtTheory.select(arVar :: indexVars : _*)

      val aStore2        = arrayStores2(key)

      and(for (aStore <- List(aStore1, aStore2)) yield {
            val storeExpr = aStore(arVar, indexVar2, ar2Var)
            val selExpr   = fromExtTheory.select(storeExpr :: indexVars : _*)

            val matrix    = ITrigger(List(selExpr),
                                     indexVar2 === indexVars(ind) |
                                       selExpr === sel2Expr)

            val compMatrix =
              if (aStore == aStore2) {
                ITrigger(List(storeExpr, sel2Expr), matrix)
              } else {
                matrix
              }

            all(varSorts, compMatrix)
          })
    })

  val allAxioms = axiom1 & axiom2 & axiom3
  
  //////////////////////////////////////////////////////////////////////////////

  override val dependencies =
    for (s <- allIndexSorts.toSeq) yield combTheories(s)

  val (predicates, axioms, _, funPredMap) =
    Theory.genAxioms(theoryFunctions = functions,
                     otherTheories   = dependencies,
                     theoryAxioms    = allAxioms)

  val totalityAxioms = Conjunction.TRUE

  val functionPredicateMapping =
    for (f <- functions) yield (f -> funPredMap(f))

  val _projections  = projections.mapValues(funPredMap(_))
  val _projections2 = projections2.mapValues(funPredMap(_))
  val _arrayStores  = arrayStores.mapValues(funPredMap(_))
  val _arrayStores2 = arrayStores2.mapValues(funPredMap(_))

  private val proj2proj2 =
    (for ((key, p) <- _projections.iterator)
     yield (p -> _projections2(key))).toMap ++
    (for ((key, p) <- _arrayStores.iterator)
     yield (p -> _arrayStores2(key))).toMap

  // just use default value
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()

  val triggerRelevantFunctions : Set[IFunction] = functions.toSet

  val functionalPredicates = predicates.toSet
  
  //////////////////////////////////////////////////////////////////////////////

  override def isSoundForSat(theories : Seq[Theory],
                             config : Theory.SatSoundnessConfig.Value) : Boolean =
    config match {
      case Theory.SatSoundnessConfig.Elementary |
           Theory.SatSoundnessConfig.Existential => true
      case Theory.SatSoundnessConfig.General     => false
    }

  //////////////////////////////////////////////////////////////////////////////

  private val pluginObj = new Plugin {

    override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
//      println(goal.facts)
      goalState(goal) match {
        case Plugin.GoalState.Eager =>
          proj2proj2Eager(goal)
        case Plugin.GoalState.Intermediate => {
          expandExtensionality(goal) elseDo
          proj2proj2Lazy(goal)
        }
        case _ =>
          List()
      }
    }

    override def computeModel(goal : Goal) : Seq[Plugin.Action] = {
//      augmentModel(goal)      elseDo
      proj2proj2Global(goal)
    }

  }

  val plugin = Some(pluginObj)

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Scan a goal for occurring array terms t, and add arrayConstant(t)
   * atoms for those. Add valueAlmostEverywhere literals for all
   * arrays that do not have a default value yet.
   */
/*
  private def augmentModel(goal : Goal) : Seq[Plugin.Action] = {
    import TerForConvenience._
    implicit val order = goal.order
    val facts = goal.facts.predConj

    val arrayConstantAtoms =
      (for ((key@(fromSorts, ind), proj) <- _projections2.iterator;
            toSorts = projSorts(key);
            a <- facts.positiveLitsWithPred(proj).iterator;
            (theory, t) <- Iterator((extTheories(fromSorts), a.head),
                                    (extTheories(toSorts),   a.last));
            b <- Iterator(conj(theory.arrayConstant(List(t))),
                          conj(existsSorted(List(theory.objSort),
                                            theory._valueAlmostEverywhere(List(t, l(v(0)))))));
            red = goal reduceWithFacts b;
            if !red.isTrue)
       yield a).toSet

    println(arrayConstantAtoms)

    for (c <- arrayConstantAtoms.toSeq)
    yield Plugin.AddFormula(Conjunction.negate(c, order))
  }
 */

  //////////////////////////////////////////////////////////////////////////////

  private val predArrayIndexes : Map[Seq[Sort],
                                     Seq[(IExpression.Predicate, Seq[Int])]] =
    (for ((indexes, arSort) <- arraySorts.iterator) yield {
       val preds =
         for (pred <- predicates;
              argSorts = MonoSortedPredicate argumentSorts pred;
              arInds = argSorts.zipWithIndex.filter(_._1 == `arSort`).map(_._2);
              if !arInds.isEmpty)
         yield (pred, arInds)
       indexes -> preds
     }).toMap

  private def expandExtensionality(goal : Goal) : Seq[Plugin.Action] =
    (for (indexSorts <- allIndexSorts.iterator;
          inds = predArrayIndexes(indexSorts);
          act <- combTheories(indexSorts).expandExtensionality(goal, 0, inds))
     yield act).toSeq

  //////////////////////////////////////////////////////////////////////////////

  // TODO: make sure those lists are sorted
  private val projectionsPerResultSort =
    (projSorts.groupBy(_._2).mapValues {
       sortList => for ((key, _) <- sortList.toSeq) yield _projections(key)
     }).withDefaultValue(List())

  private val projections2PerResultSort =
    (projSorts.groupBy(_._2).mapValues {
       sortList => for ((key, _) <- sortList.toSeq) yield _projections2(key)
     }).withDefaultValue(List())

  private val aStoresPerResultSort =
    (for (fromSorts <- allIndexSorts.iterator) yield {
       val aStores =
         for (ind <- 0 until fromSorts.size;
              p <- (_arrayStores get (fromSorts, ind)).toSeq)
         yield p
       fromSorts -> aStores
     }).toMap

  private val aStores2PerResultSort =
    (for (fromSorts <- allIndexSorts.iterator) yield {
       val aStores =
         for (ind <- 0 until fromSorts.size;
              p <- (_arrayStores2 get (fromSorts, ind)).toSeq)
         yield p
       fromSorts -> aStores
     }).toMap

  private val projections2PerArgSort =
    (_projections2.groupBy(_._1._1).mapValues {
       projList => projList map (_._2)
     }).withDefaultValue(List())

  private val aStores2PerUpdateSort =
    (projSorts.groupBy(_._2).mapValues {
       sortList => for ((key, _) <- sortList.toSeq) yield _arrayStores2(key)
     }).withDefaultValue(List())

  /**
   * When the array-valued functions form a graph that is not
   * tree-shaped, start replacing "map" with "map2" to initiate
   * bidirectional propagation
   * 
   * TODO: do we have to do something special about cycles in the
   * graph?
   */
  private def proj2proj2Lazy(goal : Goal) : Seq[Plugin.Action] = {
    (for (toSorts    <- allIndexSorts.toSeq;
          combTheory =  combTheories(toSorts);
          extTheory  =  combTheory.subTheories.head;
          act        <- proj2proj2Lazy(goal, toSorts,
                                       projections2PerResultSort(toSorts) ++
                                         aStores2PerResultSort(toSorts) ++
                                         combTheory.combinatorsPerArray.head ++
                                         combTheory.combinators2PerArray.head ++
                                         List(extTheory._store,
                                              extTheory._store2,
                                              extTheory._const), true))
     yield act) ++
    (for (toSorts      <- allIndexSorts.toSeq;
          combTheory   =  combTheories(toSorts);
          extTheory    =  combTheory.subTheories.head;
          checkedPreds =  projectionsPerResultSort(toSorts) ++
                          projections2PerResultSort(toSorts) ++
                          aStoresPerResultSort(toSorts) ++
                          aStores2PerResultSort(toSorts);
          combActs     =  combTheory.comb2comb2Lazy(goal,0,checkedPreds,false);
          extActs      =  extTheory.store2store2Lazy(goal, checkedPreds);
          act          <- combActs ++ extActs)
     yield act)
  }

  private def proj2proj2Lazy(goal         : Goal,
                             toSorts      : Seq[Sort],
                             checkedPreds : Seq[IExpression.Predicate],
                             checkProj    : Boolean)
                                          : Seq[Plugin.Action] = {
    val facts = goal.facts.predConj
    val preds = projectionsPerResultSort(toSorts) ++
                aStoresPerResultSort(toSorts)

    if (Seqs.disjointSeq(facts.predicates, preds))
      return List()

    val projAtoms = for (m <- preds;
                         a <- facts.positiveLitsWithPred(m))
                    yield a
    val allAtoms  = (if (checkProj) projAtoms else List()) ++
                    (for (p <- checkedPreds;
                          a <- facts.positiveLitsWithPred(p)) yield a)

    val needBi    = ExtArray.bidirChecker(allAtoms, goal)
    
    for (a1 <- projAtoms;
         if needBi(a1);
         action <- projConversionActions(a1, goal))
    yield action
  }

  //////////////////////////////////////////////////////////////////////////////

  private def proj2proj2Eager(goal : Goal) : Seq[Plugin.Action] = {
    (for (toSorts    <- allToSorts;
          act        <- proj2proj2Eager(goal, toSorts))
     yield act) ++
    (for (fromSorts  <- allIndexSorts.toSeq;
          combTheory =  combTheories(fromSorts);
          arrayTerms =  consumedArrayTerms(goal, fromSorts);
          act        <- combTheory.comb2comb2Eager(goal, 0, arrayTerms))
     yield act)
  }

  private def consumedArrayTerms(goal    : Goal,
                                 toSorts : Seq[Sort])
                                         : Set[LinearCombination] = {
    val facts = goal.facts.predConj
    ((for (p <- projections2PerArgSort(toSorts).iterator ++
                aStores2PerResultSort(toSorts).iterator;
           a <- facts.positiveLitsWithPred(p).iterator) yield a.head) ++ (
      for (p <- aStores2PerUpdateSort(toSorts).iterator;
           a <- facts.positiveLitsWithPred(p).iterator) yield a(2)
     )).toSet
  }

  private def proj2proj2Eager(goal    : Goal,
                              toSorts : Seq[Sort]) : Seq[Plugin.Action] = {
    val facts      = goal.facts.predConj
    val combTheory = combTheories(toSorts)

    val arrayTerms =
      combTheory.consumedArrayTerms(goal, 0) ++
      consumedArrayTerms(goal, toSorts)

    if (arrayTerms.isEmpty)
      return List()

    val couldAlias = ExtArray.aliasChecker(goal)

    for (p <- projectionsPerResultSort(toSorts) ++aStoresPerResultSort(toSorts);
         a <- facts.positiveLitsWithPred(p);
         if arrayTerms exists { t => couldAlias(t, a.last) };
         action <- projConversionActions(a, goal))
    yield action
  }

  //////////////////////////////////////////////////////////////////////////////

  private def projConversionActions(a    : Atom,
                                    goal : Goal) : Seq[Plugin.Action] = {
    implicit val order = goal.order
    import TerForConvenience._

    val newA = proj2proj2(a.pred)(a.toSeq)
    List(Plugin.RemoveFacts(a), Plugin.AddAxiom(List(a), newA, CartArray.this))
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Convert all combinators to the bi-directional version; this is
   * necessary to generate correct models.
   * 
   * TODO: determinism
   */
  private def proj2proj2Global(goal : Goal) : Seq[Plugin.Action] = {
    val facts = goal.facts.predConj
    for (p   <- _projections.values.toSeq ++ _arrayStores.values.toSeq;
         a   <- facts.positiveLitsWithPred(p);
         act <- projConversionActions(a, goal))
    yield act
  }

  //////////////////////////////////////////////////////////////////////////////

  TheoryRegistry register this

  override def toString =
    "CartArray[" + (indexSorts mkString ", ") + ", " + objSort + "]"

}
