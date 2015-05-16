/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2015 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.parser

import ap._
import ap.terfor.{ConstantTerm, TermOrder}
import ap.parameters.{PreprocessingSettings, Param}
import ap.util.Timeout
import ap.theories.TheoryRegistry

import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap}

/**
 * Preprocess an InputAbsy formula in order to make it suitable for
 * proving. The result is a list of formulae, because the original formula
 * may contain named parts (<code>INamedPart</code>).
 */
object Preprocessing {
  
  class PreprocessingException(msg : String) extends Exception(msg)

  def apply(f : IFormula,
            interpolantSpecs : List[IInterpolantSpec],
            signature : Signature,
            settings : PreprocessingSettings)
            : (List[INamedPart], List[IInterpolantSpec], Signature) = {
    val funcEnc =
      new FunctionEncoder (Param.TIGHT_FUNCTION_SCOPES(settings),
                           Param.GENERATE_TOTALITY_AXIOMS(settings) !=
                             Param.TotalityAxiomOptions.None,
                           signature.functionTypes)
    for (t <- signature.theories)
      funcEnc addTheory t
    apply(f, interpolantSpecs, signature, settings, funcEnc)
  }

  def apply(f : IFormula,
            interpolantSpecs : List[IInterpolantSpec],
            signature : Signature,
            settings : PreprocessingSettings,
            functionEncoder : FunctionEncoder)
            : (List[INamedPart], List[IInterpolantSpec], Signature) = {

    val initialSize = SizeVisitor(f)

    def checkSize(fs : Iterable[IFormula]) = {
      val newSize = (for (f <- fs.iterator) yield SizeVisitor(f)).sum
      if (newSize > 5000000 && newSize > initialSize * 5)
        throw new CmdlMain.GaveUpException("Unexpected explosion during preprocessing")
    }

    // turn the formula into a list of its named parts
    val fors = PartExtractor(f)

    // the other steps can be skipped for simple cases
    if ((functionEncoder.axioms match {
           case IBoolLit(true) => true
           case _ => false
         }) &&
        !needsPreprocessing(fors))
      return (fors, interpolantSpecs, signature)

    // partial evaluation, expand equivalences
    val fors2 =
      for (f <- fors)
      yield EquivExpander(PartialEvaluator(f)).asInstanceOf[INamedPart]
    checkSize(fors2)

    // simple mini-scoping for existential quantifiers
    val miniscoper = new SimpleMiniscoper(signature)
    val fors2b = for (f <- fors2) yield miniscoper(f)

    // compress chains of implications
//    val fors2b = for (INamedPart(n, f) <- fors2a)
//                 yield INamedPart(n, ImplicationCompressor(f))
    
    // check whether we have to add assumptions about the domain size
    val fors2a = Param.FINITE_DOMAIN_CONSTRAINTS(settings) match {
      case Param.FiniteDomainConstraints.DomainSize => {
        import IExpression._
        
        for (f <- fors2b) yield GuardIntroducingVisitor.visit(Transform2NNF(f), 0).asInstanceOf[INamedPart]
      }
      case _ =>
        fors2b
    }
    
    ////////////////////////////////////////////////////////////////////////////
    // Handling of triggers

    var order3 = signature.order
    def encodeFunctions(f : IFormula) : IFormula = {
      val (g, o) = functionEncoder(f, order3)
      order3 = o
      g
    }

    val theoryTriggerFunctions =
      (for (t <- signature.theories.iterator;
            f <- t.triggerRelevantFunctions.iterator) yield f).toSet
    // all uninterpreted functions occurring in the problem
    val problemFunctions =
      for (f <- FunctionCollector(fors2a);
           if (!(TheoryRegistry lookupSymbol f).isDefined))
      yield f

    lazy val allTriggeredFunctions = Param.TRIGGER_GENERATION(settings) match {
      case Param.TriggerGenerationOptions.None =>
        theoryTriggerFunctions
      case Param.TriggerGenerationOptions.Total =>
        theoryTriggerFunctions ++
        (for (g <- problemFunctions.iterator;
              if (!g.partial && !g.relational)) yield g)
      case _ =>
        theoryTriggerFunctions ++ problemFunctions
    }
    lazy val stdTriggerGenerator = {
      val gen = new TriggerGenerator (allTriggeredFunctions,
                                      Param.TRIGGER_STRATEGY(settings))
      for (f <- fors2a)
        gen setup f
      gen
    }

    val fors3 = Param.TRIGGER_GENERATION(settings) match {
      case Param.TriggerGenerationOptions.Complete |
           Param.TriggerGenerationOptions.CompleteFrugal => {

        val disjuncts =
          (for (INamedPart(n, f) <- fors2a.iterator;
                f2 <- LineariseVisitor(Transform2NNF(f), IBinJunctor.Or).iterator)
           yield (INamedPart(n, f2))).toArray
  
        val coll = new TotalFunctionCollector(functionEncoder.predTranslation,
                                              signature.domainPredicates)
  
        val impliedTotalFunctions =
          for (d@INamedPart(n, f) <- disjuncts) yield
            if (f.isInstanceOf[IQuantified])
              // translation without triggers
              (d, coll(encodeFunctions(f)) & problemFunctions)
            else
              (d, Set[IFunction]())
  
        val functionOccurrences = new MHashMap[IFunction, Int]
        for ((_, s) <- impliedTotalFunctions.iterator; f <- s.iterator)
          functionOccurrences.put(f, functionOccurrences.getOrElse(f, 0) + 1)

        def updateFunctionOccurrences(oldFuns : Set[IFunction],
                                      newDisjunct : IFormula) = {
          for (f <- oldFuns)
            functionOccurrences.put(f, functionOccurrences(f) - 1)
          for (f <- coll(newDisjunct))
            if (problemFunctions contains f)
              functionOccurrences.put(f, functionOccurrences(f) + 1)
        }

        // add the functions for which explicit totality axioms will be created
        if (Param.GENERATE_TOTALITY_AXIOMS(settings) !=
              Param.TotalityAxiomOptions.None)
          for (f <- problemFunctions)
            if (!f.partial)
              functionOccurrences.put(f, functionOccurrences.getOrElse(f, 0) + 1)

        val totalFunctions =
          theoryTriggerFunctions ++
          (for (f <- problemFunctions.iterator;
                if ((functionOccurrences get f) match {
                      case Some(n) => n > 0
                      case None => false
                    }))
           yield f)

        val newDisjuncts = Param.TRIGGER_GENERATION(settings) match {
          case Param.TriggerGenerationOptions.Complete => {
            val triggeredNonTotal = allTriggeredFunctions -- totalFunctions

            for ((INamedPart(n, disjunct), funs) <- impliedTotalFunctions) yield {
              val withTriggers =
                if (!disjunct.isInstanceOf[IQuantified] ||
                    (!ContainsSymbol(disjunct, (f:IExpression) => f match {
                        case IFunApp(f, _) => triggeredNonTotal contains f
                        case _ => false
                      }) &&
                     !(funs exists { f => functionOccurrences(f) == 1 }))) {
                  // can generate triggers for all functions that were identified
                  // as total
                  stdTriggerGenerator(disjunct)
                } else {
                  // add a version of this formula without triggers
                  stdTriggerGenerator(disjunct) | disjunct
                }

/*
println(functionOccurrences.toList)
println((INamedPart(n, disjunct), funs))
println(withTriggers)
println
*/

              val encoded = encodeFunctions(withTriggers)
              updateFunctionOccurrences(funs, encoded)

              INamedPart(n, encoded)
            }
          }

          case Param.TriggerGenerationOptions.CompleteFrugal => {
            // only use total functions in triggers
            val triggerGenerator =
              new TriggerGenerator (totalFunctions,
                                    Param.TRIGGER_STRATEGY(settings))
            for (f <- fors2a)
              triggerGenerator setup f

            val triggerInjector =
              new EmptyTriggerInjector(signature.domainPredicates)

            for ((INamedPart(n, disjunct), funs) <- impliedTotalFunctions) yield {
              val withTriggers =
                if (!disjunct.isInstanceOf[IQuantified] ||
                    !(funs exists { f => functionOccurrences(f) == 1 })) {
                  // can generate triggers for all functions that were identified
                  // as total
                  triggerGenerator(disjunct)
                } else {
                  // cannot introduce triggers on top-level, since this disjunct
                  // is needed to demonstrate totality of some function
                  triggerGenerator(triggerInjector(disjunct))
                }

              val encoded = encodeFunctions(withTriggers)
              updateFunctionOccurrences(funs, encoded)

/*
println(functionOccurrences.toList)
println((INamedPart(n, disjunct), funs))
println(withTriggers)
println(encoded)
println
*/

              INamedPart(n, encoded)
            }
          }
        }

        PartExtractor(IExpression.or(newDisjuncts))
      }

      case _ => {
        val withTriggers = for (f <- fors2a) yield stdTriggerGenerator(f)

        for (INamedPart(n, f) <- withTriggers)
        yield INamedPart(n, encodeFunctions(f))
      }
    }

    ////////////////////////////////////////////////////////////////////////////
    // Add the function axioms

    val fors4 = functionEncoder.axioms match {
      case IBoolLit(true) => fors3
      case x => {
        var noNamePart : INamedPart = null
        var realNamedParts : List[INamedPart] = List()
        
        for (p @ INamedPart(n, _) <- fors3)
          if (n == PartName.NO_NAME)
            noNamePart = p
          else
            realNamedParts = p :: realNamedParts
        
        val newNoNamePart = noNamePart match {
          case null => INamedPart(PartName.NO_NAME, !x)
          case INamedPart(_, f) => INamedPart(PartName.NO_NAME, f | !x)
        }
        newNoNamePart :: realNamedParts
      }
    }
    checkSize(fors4)

    // do some direct simplifications
    val fors5 = 
      for (f <- fors4) yield BooleanCompactifier(f).asInstanceOf[INamedPart]
    
    // do clausification
    val fors6 = Param.CLAUSIFIER(settings) match {
      case Param.ClausifierOptions.None =>
        fors5
      case Param.ClausifierOptions.Simple =>
        Timeout.withTimeoutMillis(Param.CLAUSIFIER_TIMEOUT(settings))(
          for (f <- fors5) yield (new SimpleClausifier)(f).asInstanceOf[INamedPart]
        )(throw new CmdlMain.GaveUpException("Clausification timed out"))
    }
    checkSize(fors6)
    
    (fors6, interpolantSpecs, signature updateOrder order3)
  }

  //////////////////////////////////////////////////////////////////////////////

  private def needsPreprocessing(fors : List[INamedPart]) : Boolean = try {
    val visitor = new ComplicatedOpVisitor
    for (INamedPart(_, f) <- fors) visitor.visitWithoutResult(f, ())
    false
  } catch {
    case NeedsPreprocException => true
  }

  private object NeedsPreprocException extends Exception

  private class ComplicatedOpVisitor extends CollectingVisitor[Unit, Unit] {
    private var opNum = 0
    override def preVisit(t : IExpression, arg : Unit) : PreVisitResult = {
      opNum = opNum + 1
      if (opNum > 500)
        throw NeedsPreprocException

      t match {
        case _ : IConstant | _ : IIntLit | _ : IPlus | _ : ITimes |
             _ : IAtom | _ : IBoolLit | _ : IIntFormula | _ : INot |
             IBinFormula(IBinJunctor.And | IBinJunctor.Or, _, _) => KeepArg
        case _ => throw NeedsPreprocException
      }
    }
    def postVisit(t : IExpression, arg : Unit, subres : Seq[Unit]) : Unit = ()
  }
  
}

////////////////////////////////////////////////////////////////////////////////

private object GuardIntroducingVisitor extends CollectingVisitor[Int, IFormula] {

  import IExpression._
  
  override def preVisit(t : IExpression, quans : Int) : PreVisitResult = t match {
    case LeafFormula(t) =>
      ShortCutResult(t)
    case IQuantified(Quantifier.ALL, _) =>
      UniSubArgs(quans + 1)
    case _ =>
      UniSubArgs(0)
  }
  
  def postVisit(t : IExpression, quans : Int, subres : Seq[IFormula]) : IFormula =
    (t, quans) match {
      case (t@IQuantified(Quantifier.ALL, _), _) =>
        t update subres
      case (t : IFormula, quans) if (quans > 0) => {
        // add guards for the quantified formulae
        val guards = connect(
          for (i <- 0 until quans) yield (v(i) >= 0 & v(i) < CmdlMain.domain_size),
          IBinJunctor.And)
        
        guards ==> (t update subres)
      }
      case (t : IFormula, _) =>
        t update subres
    }
  
}

////////////////////////////////////////////////////////////////////////////////

import ap.terfor.conjunctions.Quantifier

/**
 * Visitor that determines functions whose totality is implied by a
 * quantified formula.
 */
private class TotalFunctionCollector(
        predTranslation : scala.collection.Map[IExpression.Predicate, IFunction],
        domainPredicates : Set[IExpression.Predicate])
              extends ContextAwareVisitor[Unit, Unit] {

  private val collectedFunctions = new MHashSet[IFunction]

  def apply(f : IFormula) : Set[IFunction] = {
    this.visitWithoutResult(f, Context(()))
    val res = collectedFunctions.toSet
    collectedFunctions.clear
    res
  }

  override def preVisit(t : IExpression,
                        ctxt : Context[Unit]) : PreVisitResult = t match {
    case _ : IQuantified | _ : INot =>
      super.preVisit(t, ctxt)
    case IBinFormula(IBinJunctor.And, IAtom(dp, _), _)
      if (ctxt.polarity > 0 && (domainPredicates contains dp)) =>
        super.preVisit(t, ctxt)
    case IBinFormula(IBinJunctor.And, _, _)
      if (ctxt.polarity < 0) =>
        super.preVisit(t, ctxt)
    case IBinFormula(IBinJunctor.Or, _, _)
      if (ctxt.polarity > 0) =>
        super.preVisit(t, ctxt)

    case IAtom(p, args)
      if (ctxt.polarity < 0) => (predTranslation get p) match {
        case Some(f) => {
          // the function arguments have to be existentially quantified

          val exIndexes =
            (for (IVariable(ind) <- args.init.iterator;
                  if (ctxt.binders(ind) == Context.EX))
             yield ind).toSet
          if (exIndexes.size == args.size - 1)
            collectedFunctions += f

          ShortCutResult(())
        }
        case None =>
          ShortCutResult(())
      }
    case _ =>
      ShortCutResult(())
  }

  def postVisit(t : IExpression, ctxt : Context[Unit],
                subres : Seq[Unit]) : Unit = ()

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Visitor to add an empty trigger set for every top-level existential
 * quantifier. This assumes that the given formula is in NNF.
 */
private class EmptyTriggerInjector(domainPredicates : Set[IExpression.Predicate])
        extends CollectingVisitor[Boolean, IExpression] {

  def apply(f : IFormula) : IFormula =
    this.visit(f, false).asInstanceOf[IFormula]

  override def preVisit(t : IExpression,
                        underEx : Boolean) : PreVisitResult = t match {
    case IQuantified(Quantifier.EX, _) =>
      UniSubArgs(true)
    case IBinFormula(IBinJunctor.And, IAtom(dp, _), _)
      if (domainPredicates contains dp) =>
        UniSubArgs(false)
    case _ : IQuantified |
         IBinFormula(IBinJunctor.Or, _, _) |
         _ : ITrigger =>
      UniSubArgs(false)
    case t : IFormula =>
      ShortCutResult(if (underEx) ITrigger(List(), t) else t)
  }

  def postVisit(t : IExpression, underEx : Boolean,
                subres : Seq[IExpression]) : IExpression = t match {
    case _ : ITrigger | IQuantified(Quantifier.EX, _) =>
      t update subres
    case t : IFormula if (underEx) =>
      ITrigger(List(), t update subres)
    case t =>
      t update subres
  }

}
