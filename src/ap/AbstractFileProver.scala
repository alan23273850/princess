/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.parser.{InputAbsy2Internal, Parser2InputAbsy, Preprocessing,
                  IExpression, INamedPart, IFunction, IInterpolantSpec, Environment}
import ap.terfor.{Formula, TermOrder}
import ap.terfor.conjunctions.{Conjunction, Quantifier, ReduceWithConjunction}
import ap.proof.{ModelSearchProver, ExhaustiveProver, ConstraintSimplifier}
import ap.proof.tree.ProofTree
import ap.proof.goal.{Goal, SymbolWeights}
import ap.proof.certificates.Certificate
import ap.util.{Debug, Timeout}

abstract class AbstractFileProver(reader : java.io.Reader, output : Boolean,
                                  timeout : Int, userDefStoppingCond : => Boolean,
                                  settings : GlobalSettings) {

  protected def println(str : => String) : Unit = (if (output) Predef.println(str))
  
  private def determineTriggerGenFunctions(settings : GlobalSettings,
                                           env : Environment)
                                          : Set[IFunction] =
    Param.TRIGGER_GENERATION(settings) match {
      case Param.TriggerGenerationOptions.None => Set()
      case Param.TriggerGenerationOptions.All => env.nonNullaryFunctions
      case Param.TriggerGenerationOptions.Total =>
        for (f <- env.nonNullaryFunctions; if (!f.partial && !f.relational))
          yield f
    }
  
  val (inputFormulas, interpolantSpecs, signature) = {
    val env = new Environment
    val (f, interpolantSpecs, signature) = Parser2InputAbsy(reader, env)
    reader.close
    
    val preprocSettings =
       Param.TRIGGER_GENERATOR_CONSIDERED_FUNCTIONS.set(
           settings.toPreprocessingSettings,
           determineTriggerGenFunctions(settings, env))

    Console.withOut(Console.err) {
      println("Preprocessing ...")
    }
    Preprocessing(f, interpolantSpecs, signature, preprocSettings)
  }
  
  private val constructProofs = Param.PROOF_CONSTRUCTION_GLOBAL(settings) match {
    case Param.ProofConstructionOptions.Never => false
    case Param.ProofConstructionOptions.Always => true
    case Param.ProofConstructionOptions.IfInterpolating => !interpolantSpecs.isEmpty
  }
    
  val order = signature.order
  
  private val reducer = ReduceWithConjunction(Conjunction.TRUE, order)
  
  private def simplify(f : Conjunction) : Conjunction =
    // if we are constructing proofs, we simplify formulae right away
    if (constructProofs) reducer(f) else f

  val formulas =
    for (f <- inputFormulas) yield
      simplify(
        Conjunction.conj(InputAbsy2Internal(IExpression removePartName f, order),
                         order))

  //////////////////////////////////////////////////////////////////////////////
  
  protected val goalSettings =
    Param.PROOF_CONSTRUCTION.set(
    Param.SYMBOL_WEIGHTS.set(
    Param.CONSTRAINT_SIMPLIFIER.set(settings.toGoalSettings,
                             determineSimplifier(settings)),
                             SymbolWeights.normSymbolFrequencies(formulas, 1000)),
                             constructProofs)
  
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

  lazy val namedParts =
    Map() ++ (for ((INamedPart(name, _), f) <-
                   inputFormulas.iterator zip formulas.iterator)
              yield (name -> f))
  
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
  
  protected def findCounterModelTimeout(f : Seq[Conjunction]) = {
    val timeBefore = System.currentTimeMillis
    val stoppingCond = () => {
      if ((System.currentTimeMillis - timeBefore > timeout) || userDefStoppingCond)
        Timeout.raise
    }

    Timeout.withChecker(stoppingCond) {
      ModelSearchProver(f, order, goalSettings)
    }
  }
  
  protected def findModel(f : Conjunction) : Conjunction =
    ModelSearchProver(f.negate, f.order)
  
  protected def constructProofTree(mostGeneralConstraint : Boolean)
                                  : (ProofTree, Boolean) = {
    // explicitly quantify all universal variables
    
    val closedFor = Conjunction.quantify(Quantifier.ALL,
                                         order sort signature.nullaryFunctions,
                                         Conjunction.disj(formulas, order), order)
    
    Console.withOut(Console.err) {
      println("Proving ...")
    }
    
    val timeBefore = System.currentTimeMillis
    val stoppingCond = () => {
      if ((System.currentTimeMillis - timeBefore > timeout) ||
          userDefStoppingCond)
        Timeout.raise
    }

    Timeout.withChecker(stoppingCond) {
      val prover = new ExhaustiveProver(!mostGeneralConstraint, goalSettings)
      val tree = prover(closedFor, signature)
      val validConstraint = prover.isValidConstraint(tree.closingConstraint, signature)
      (tree, validConstraint)
    }
  }
}
