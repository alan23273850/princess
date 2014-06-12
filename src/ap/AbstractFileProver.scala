/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2014 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap;

import ap.parameters._
import ap.parser.{InputAbsy2Internal,
                  ApParser2InputAbsy, SMTParser2InputAbsy, TPTPTParser,
                  Preprocessing,
                  FunctionEncoder, IExpression, INamedPart, PartName,
                  IFunction, IInterpolantSpec, IBinJunctor, Environment}
import ap.terfor.{Formula, TermOrder}
import ap.terfor.conjunctions.{Conjunction, Quantifier, ReduceWithConjunction}
import ap.terfor.preds.Predicate
import ap.proof.{ModelSearchProver, ExhaustiveProver, ConstraintSimplifier}
import ap.proof.tree.ProofTree
import ap.proof.goal.{Goal, SymbolWeights}
import ap.proof.certificates.Certificate
import ap.util.{Debug, Timeout}

object AbstractFileProver {
  
  private val AC = Debug.AC_MAIN
  
}

abstract class AbstractFileProver(reader : java.io.Reader, output : Boolean,
                                  timeout : Int, userDefStoppingCond : => Boolean,
                                  settings : GlobalSettings) extends Prover {

  private val startTime = System.currentTimeMillis

  private val stoppingCond = () => {
    if ((System.currentTimeMillis - startTime > timeout) || userDefStoppingCond)
      Timeout.raise
  }

  protected def println(str : => String) : Unit = (if (output) Predef.println(str))
  
  private def determineTriggerGenFunctions[CT,VT,PT,FT]
                                          (settings : GlobalSettings,
                                           env : Environment[CT,VT,PT,FT],
                                           signature : Signature)
                                          : Set[IFunction] =
    Param.TRIGGER_GENERATION(settings) match {
      case Param.TriggerGenerationOptions.None => Set()
      case Param.TriggerGenerationOptions.All =>
        env.nonNullaryFunctions -- (
          // remove interpreted functions
          for (t <- signature.theories.iterator;
               f <- t.functions.iterator;
               if (f.partial || f.relational)) yield f)
      case Param.TriggerGenerationOptions.Total =>
        for (f <- env.nonNullaryFunctions; if (!f.partial && !f.relational))
          yield f
    }
  
  private def newParser = Param.INPUT_FORMAT(settings) match {
    case Param.InputFormat.Princess => ApParser2InputAbsy(settings.toParserSettings)
    case Param.InputFormat.SMTLIB => SMTParser2InputAbsy(settings.toParserSettings)
    case Param.InputFormat.TPTP => TPTPTParser(settings.toParserSettings)
  }
  
  val (inputFormulas, originalInputFormula,
       interpolantSpecs, signature, gcedFunctions, functionEncoder) = {
    val parser = newParser
    val (f, interpolantSpecs, signature) = parser(reader)
    reader.close
    
    val preprocSettings =
       Param.TRIGGER_GENERATOR_CONSIDERED_FUNCTIONS.set(
           settings.toPreprocessingSettings,
           determineTriggerGenFunctions(settings, parser.env, signature))

    Console.withOut(Console.err) {
      println("Preprocessing ...")
    }
    
    val functionEnc =
      new FunctionEncoder (Param.TIGHT_FUNCTION_SCOPES(settings),
                           Param.GENERATE_TOTALITY_AXIOMS(settings))
    for (t <- signature.theories)
      functionEnc addTheory t

    val (inputFormulas, interpolantS, sig) =
      Preprocessing(f, interpolantSpecs, signature, preprocSettings, functionEnc)
    
    val gcedFunctions = Param.FUNCTION_GC(settings) match {
      case Param.FunctionGCOptions.None =>
        Set[Predicate]()
      case Param.FunctionGCOptions.Total =>
        (for ((p, f) <- functionEnc.predTranslation.iterator; if (!f.partial))
          yield p).toSet
      case Param.FunctionGCOptions.All =>
        functionEnc.predTranslation.keySet.toSet
    }
    
    val oriFormula =
      // only store unprocessed input formula if we plan to print it later
      if (Param.PRINT_SMT_FILE(settings) != "" ||
          Param.PRINT_TPTP_FILE(settings) != "")  f else null

    (inputFormulas, oriFormula, interpolantS, sig, gcedFunctions, functionEnc)
  }
  
  private val functionalPreds = 
    (for ((p, f) <- functionEncoder.predTranslation.iterator;
          if (!f.relational)) yield p).toSet
  
  private val plugins = for (t <- signature.theories; p <- t.plugin.toSeq) yield p
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertInt(AbstractFileProver.AC, plugins.size <= 1)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  private val constructProofs = Param.PROOF_CONSTRUCTION_GLOBAL(settings) match {
    case Param.ProofConstructionOptions.Never => false
    case Param.ProofConstructionOptions.Always => true
    case Param.ProofConstructionOptions.IfInterpolating => !interpolantSpecs.isEmpty
  }
    
  val order = signature.order

  private val theoryAxioms =
    Conjunction.conj(for (t <- signature.theories) yield t.axioms, order).negate

  private val reducer =
    ReduceWithConjunction(Conjunction.TRUE, functionalPreds, order)

  private val allPartNames =
    (List(PartName.NO_NAME) ++
     (for (INamedPart(n, _) <- inputFormulas) yield n)).distinct
  
  val (namedParts, formulas) =
    if (constructProofs) {
      // keep the different formula parts separate
      val rawNamedParts =
        Map(PartName.NO_NAME -> Conjunction.FALSE) ++
        (for (INamedPart(n, f) <- inputFormulas.iterator)
         yield (n -> Conjunction.conj(InputAbsy2Internal(f, order), order)))
      val reducedNamedParts =
        for ((n, c) <- rawNamedParts) yield n match {
          case PartName.NO_NAME =>
            (PartName.NO_NAME ->
             reducer(Conjunction.disj(List(theoryAxioms, c), order)))
          case n =>
            (n -> reducer(c))
        }

      (reducedNamedParts,
       for (n <- allPartNames) yield reducedNamedParts(n))
    } else {
      // merge everything into one formula
      val f =
        reducer(Conjunction.disjFor(
               List(theoryAxioms,
                    InputAbsy2Internal(
                      IExpression.or(
                         for (f <- inputFormulas.iterator)
                         yield (IExpression removePartName f)), order)), order))
      (Map(PartName.NO_NAME -> f), List(f))
    }

  //////////////////////////////////////////////////////////////////////////////
  
  protected val goalSettings = {
    var gs = settings.toGoalSettings
    gs = Param.CONSTRAINT_SIMPLIFIER.set(gs, determineSimplifier(settings))
    gs = Param.SYMBOL_WEIGHTS.set(gs, SymbolWeights.normSymbolFrequencies(formulas, 1000))
    gs = Param.PROOF_CONSTRUCTION.set(gs, constructProofs)
    gs = Param.GARBAGE_COLLECTED_FUNCTIONS.set(gs, gcedFunctions)
    gs = Param.FUNCTIONAL_PREDICATES.set(gs, functionalPreds)
    gs = Param.SINGLE_INSTANTIATION_PREDICATES.set(gs,
           (for (t <- signature.theories.iterator;
                 p <- t.singleInstantiationPredicates.iterator) yield p).toSet)
    gs = Param.PREDICATE_MATCH_CONFIG.set(gs, signature.predicateMatchConfig)
    gs = Param.THEORY_PLUGIN.set(gs, plugins.headOption)
    gs
  }
  
  private def determineSimplifier(settings : GlobalSettings) : ConstraintSimplifier =
    Param.SIMPLIFY_CONSTRAINTS(settings) match {
      case Param.ConstraintSimplifierOptions.None =>
        ConstraintSimplifier.NO_SIMPLIFIER
      case x =>
        ConstraintSimplifier(x == Param.ConstraintSimplifierOptions.Lemmas,
                             Param.DNF_CONSTRAINTS(settings),
                             Param.TRACE_CONSTRAINT_SIMPLIFIER(settings))
    }
  
  //////////////////////////////////////////////////////////////////////////////

  protected def findModelTimeout : Either[Conjunction, Certificate] = {
    Console.withOut(Console.err) {
      println("Constructing satisfying assignment for the existential constants ...")
    }
    findCounterModelTimeout(List(Conjunction.disj(formulas, order).negate))
  }
  
  protected def findCounterModelTimeout : Either[Conjunction, Certificate] = {
    Console.withOut(Console.err) {
      println("Constructing countermodel ...")
    }
    findCounterModelTimeout(if (formulas exists (_.isTrue))
                              List(Conjunction.TRUE)
                            else
                              formulas)
  }
  
  protected def findCounterModelTimeout(f : Seq[Conjunction]) =
    Timeout.withChecker(stoppingCond) {
      ModelSearchProver(f, order, goalSettings)
    }
  
  protected def findModel(f : Conjunction) : Conjunction =
    ModelSearchProver(f.negate, f.order)
  
  protected def constructProofTree : (ProofTree, Boolean) = {
    // explicitly quantify all universal variables
    
    val closedFor = Conjunction.quantify(Quantifier.ALL,
                                         order sort signature.nullaryFunctions,
                                         Conjunction.disj(formulas, order), order)
    
    Console.withOut(Console.err) {
      println("Proving ...")
    }
    
    Timeout.withChecker(stoppingCond) {
      val prover =
        new ExhaustiveProver(!Param.MOST_GENERAL_CONSTRAINT(settings), goalSettings)
      val tree = prover(closedFor, signature)
      val validConstraint = prover.isValidConstraint(tree.closingConstraint, signature)
      (tree, validConstraint)
    }
  }
}
