/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2020 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
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

package ap.theories.rationals

import ap.parser._
import ap.basetypes.IdealInt
import ap.theories._
import ap.algebra.{Ring, RingWithDivision, IntegerRing, Field, OrderedRing}
import ap.types.{Sort, ProxySort, MonoSortedIFunction}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.Signature

import scala.collection.{Map => GMap}
import scala.collection.mutable.{Map => MMap, Set => MSet}

/**
 * The theory of fractions <code>s / t</code>, with <code>s, t</code>
 * taken from some ring. The theory uses an encoding in which the same
 * (fixed, but arbitrary) denominator is used for all expressions. The
 * range of considered denominators is described by the
 * <code>denomConstraint</code> argument over the variable <code>_0</code>.
 */
class Fractions(name : String,
                underlyingRing : Ring,
                denomConstraint : IFormula)
      extends Theory with RingWithDivision {

  import underlyingRing.{dom => RingSort, mul => ringMul}

  private val ringZero = underlyingRing.zero
  private val ringOne  = underlyingRing.one

  /**
   * Method that can be overwritten in sub-classes to term concrete
   * fractions into canonical form.
   */
  protected def simplifyFraction(n : ITerm, d : ITerm) : (ITerm, ITerm) = (n, d)

  object FractionSort extends ProxySort (RingSort) {

    override val name = Fractions.this.name

    override def decodeToTerm(
                   d : IdealInt,
                   assign : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
      assign get ((d, this))

    override def augmentModelTermSet(
                   model : Conjunction,
                   assignment : MMap[(IdealInt, Sort), ITerm],
                   allTerms : Set[(IdealInt, Sort)],
                   definedTerms : MSet[(IdealInt, Sort)]) : Unit = {
      for (LinearCombination.Constant(d) <-
             model.predConj.lookupFunctionResult(_denom, List());
           denomTerm <-
             RingSort.decodeToTerm(d, assignment))
        for (p@(num, `dom`) <- allTerms;
             numTerm <- RingSort.decodeToTerm(num, assignment)) {
          val (n, d) = simplifyFraction(numTerm, denomTerm)
          assignment.put(p, IFunApp(frac, List(n, d)))
        }

      // TODO: add terms to definedTerms?
      super.augmentModelTermSet(model, assignment, allTerms, definedTerms)
    }
  }

  val dom : Sort = FractionSort

  /**
   * Function to represent fractions, where numerator and denominator
   * are expressions from the underlying ring
   */
  val frac : IFunction =
    MonoSortedIFunction(name + "_frac", List(RingSort, RingSort), dom,
                        true, false)

  /**
   * Extractor for fractions, where numerator and denominator
   * are expressions from the underlying ring
   */
  object Fraction {
    def apply(num : ITerm, denom : ITerm) : ITerm =
      IFunApp(frac, List(num, denom))
    def unapply(t : ITerm) : Option[(ITerm, ITerm)] = t match {
      case IFunApp(`frac`, Seq(num, denom)) => Some((num, denom))
      case _                                => None
    }
  }

  /**
   * Function used internally to represent the unique denominator for all
   * fractions
   */
  val denom : IFunction =
    MonoSortedIFunction(name + "_denom", List(), RingSort,
                        true, false)

  val functions = List(frac, denom)

  val (predicates, axioms, _, _) =
    Theory.genAxioms(theoryFunctions = functions)

  val functionPredicateMapping = functions zip predicates
  val totalityAxioms = Conjunction.TRUE
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()
  val triggerRelevantFunctions : Set[IFunction] = functions.toSet
  val functionalPredicates = predicates.toSet
  val plugin = None

  private val _denom : IExpression.Predicate = predicates(1)

  override def iPreprocess(f : IFormula, signature : Signature)
                        : (IFormula, Signature) =
    (Preprocessor.visit(f, ()).asInstanceOf[IFormula], signature)

  override def isSoundForSat(theories : Seq[Theory],
                             config : Theory.SatSoundnessConfig.Value)
                           : Boolean = true

  import IExpression._

  def int2ring(s: ITerm): ITerm =
    frac(underlyingRing.int2ring(s), ringOne)

  val zero: ITerm = frac(ringZero, ringOne)
  val one : ITerm = frac(ringOne, ringOne)

  def plus(s: ITerm, t: ITerm): ITerm = (s, t) match {
    case (IFunApp(`frac`, Seq(num1, denom1)),
          IFunApp(`frac`, Seq(num2, denom2))) if denom1 == denom2 =>
      frac(underlyingRing.plus(num1, num2), denom1)
    case _ =>
      underlyingRing.plus(s, t)
  }

  def mul (s: ITerm, t: ITerm): ITerm = (s, t) match {
    case (IFunApp(`frac`, Seq(num1, denom1)),
          IFunApp(`frac`, Seq(num2, denom2))) =>
      frac(ringMul(num1, num2), ringMul(denom1, denom2))
    case (IFunApp(`frac`, Seq(IIntLit(num), `ringOne`)), t) =>
      times(num, t)
    case (t, IFunApp(`frac`, Seq(IIntLit(num), `ringOne`))) =>
      times(num, t)
    case (s, t) =>
      // (s / denom) * (t / denom) =
      // s * t / denom^2 =
      // (s * t / denom) / denom
      eps(ex((denom() === v(0)) & denomConstraint &
             (ringMul(v(0), v(1)) ===
                ringMul(VariableShiftVisitor(s, 0, 2),
                        VariableShiftVisitor(t, 0, 2)))))
  }

  override def times(num : IdealInt, s : ITerm) : ITerm = s match {
    case IFunApp(`frac`, Seq(n, d)) =>
      frac(underlyingRing.times(num, n), d)
    case s =>
      underlyingRing.times(num, s)
  }

  def div(s : ITerm, t : ITerm) : ITerm = t match {
    case IFunApp(`frac`, Seq(n, d)) =>
      mul(s, frac(d, n))
    case t =>
      // (s / denom) / (t / denom) =
      // (s / denom) * (denom / t) =
      // (s * denom / t) / denom
      eps(ex((denom() === v(0)) & denomConstraint &
             (ringMul(VariableShiftVisitor(t, 0, 2), v(1)) ===
                ringMul(VariableShiftVisitor(s, 0, 2), v(0)))))
  }

  def minus(s: ITerm): ITerm = s match {
    case IFunApp(`frac`, Seq(n, d)) =>
      frac(underlyingRing.minus(n), d)
    case s =>
      underlyingRing.minus(s)
  }

  private object Preprocessor extends CollectingVisitor[Unit, IExpression] {
    def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[IExpression]) : IExpression = t match {
      case IFunApp(`frac`, _) =>
        subres match {
          case Seq(num : ITerm, den : ITerm) =>
            eps(ex(ex((denom() === v(0)) & denomConstraint &
                    (v(0) === ringMul(v(1), VariableShiftVisitor(den, 0, 3))) &
                    (v(2) === ringMul(v(1), VariableShiftVisitor(num, 0, 3))))))
        }
      case _ =>
        t update subres
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  TheoryRegistry register this

  override def toString = name

}

/**
 * The theory and field of rational numbers.
 */
object Rationals extends Fractions("Rat", IntegerRing, IExpression.v(0) > 0)
                 with Field with OrderedRing {

  override val dependencies = List(GroebnerMultiplication)

  protected override
    def simplifyFraction(n : ITerm, d : ITerm) : (ITerm, ITerm) = (n, d) match {
      case (IIntLit(n), IIntLit(d)) => {
        val l = n gcd d
        (IIntLit(n / l), IIntLit(d / l))
      }
      case _ =>
        (n, d)
    }

  def lt(s : ITerm, t : ITerm) : IFormula = s < t

  def leq(s : ITerm, t : ITerm) : IFormula = s <= t

}

