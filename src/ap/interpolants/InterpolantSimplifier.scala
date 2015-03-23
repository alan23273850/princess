/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2010-2015 Philipp Ruemmer <ph_r@gmx.net>
 *                         Angelo Brillout <bangelo@inf.ethz.ch>
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

package ap.interpolants

import ap._
import ap.basetypes.IdealInt
import ap.parser._
import ap.theories.SimpleArray


/**
 * Extended version of the InputAbsy simplifier that also rewrites certain
 * array expressions:
 *    \exists int a; x = store(a, b, c)
 * is replaced with
 *    select(x, b) = c 
 */
class InterpolantSimplifier(select : IFunction, store : IFunction)
      extends ap.parser.Simplifier {
  import IBinJunctor._
  import IIntRelation._
  import IExpression._
  import Quantifier._

  private class StoreRewriter(depth : Int) {
    var foundProblem : Boolean = false
    var storeArgs : Option[(ITerm, ITerm)] = None

    def rewrite(t : ITerm) : ITerm = t match {
      case IPlus(t1, t2) => rewrite(t1) +++ rewrite(t2)
      case IFunApp(`store`, Seq(IVariable(`depth`), t1, t2)) => {
        if (storeArgs != None)
          foundProblem = true
        storeArgs = Some(shiftVariables(t1), shiftVariables(t2))
        0
      }
      case _ => shiftVariables(t)
    }
    
    private def shiftVariables(t : ITerm) : ITerm = {
      if ((SymbolCollector variables t) contains IVariable(depth))
        foundProblem = true
      VariableShiftVisitor(t, depth + 1, -1)
    }
  }
  
  private def rewriteEquation(t : ITerm, depth : Int) : Option[IFormula] = {
    val rewriter = new StoreRewriter(depth)
    val newT = rewriter rewrite t

    rewriter.storeArgs match {
      case Some((t1, t2)) if (!rewriter.foundProblem) =>
        Some(select(-newT, t1) === t2)
      case _ =>
        None
    }
  }
  
  private def translate(f : IFormula,
                        negated : Boolean,
                        depth : Int) : Option[IFormula] = f match {
      
    case IQuantified(q, subF) if (q == Quantifier(negated)) =>
      for (res <- translate(subF, negated, depth + 1)) yield IQuantified(q, res)
        
    case IIntFormula(EqZero, t) if (!negated) =>
      rewriteEquation(t, depth)
    
    case INot(IIntFormula(EqZero, t)) if (negated) =>
      for (f <- rewriteEquation(t, depth)) yield !f
        
    case _ => None
  }
  
  private def elimStore(expr : IExpression) : IExpression = expr match {
    case IQuantified(EX, f) =>  translate(f, false, 0) getOrElse expr
    case IQuantified(ALL, f) => translate(f, true, 0) getOrElse expr
    case _ => expr
  }

  protected override def furtherSimplifications(expr : IExpression) = elimStore(expr)
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Even more extended version of the InputAbsy simplifier that also
 * rewrites certain array expressions:
 *    \exists int a; (x = store(a, b, c) & phi)
 * is replaced with
 *    \exists int d, a; (select(x, b) = c & a = store(x, b, d) & phi)
 */
object ArraySimplifier extends ap.parser.Simplifier {
  import IBinJunctor._
  import IIntRelation._
  import IExpression._
  import Quantifier._

  private def translate(f : IFormula,
                        negated : Boolean,
                        depth : Int) : Option[IFormula] = {

    def shiftTerm(t : ITerm) : ITerm       = VariableShiftVisitor(t, depth + 1, 1)
    def shiftFor (f : IFormula) : IFormula = VariableShiftVisitor(f, depth + 1, 1)

    f match {
      case IQuantified(q, subF) if (q == Quantifier(negated)) =>
        for (res <- translate(subF, negated, depth + 1)) yield IQuantified(q, res)
  
      case IBinFormula(j, left, right)
          if (j == (if (negated) IBinJunctor.Or else IBinJunctor.And)) =>
        (for (newLeft <- translate(left, negated, depth))
         yield IBinFormula(j, newLeft, shiftFor(right))) orElse
        (for (newRight <- translate(right, negated, depth))
         yield IBinFormula(j, shiftFor(left), newRight))
  
      case INot(f) =>
        for (res <- translate(f, !negated, depth)) yield INot(res)

      case Eq(IFunApp(SimpleArray.Store(),
                      Seq(w@IVariable(`depth`), args @ _*)), ar)
          if (!negated && !ContainsSymbol(ar, w) &&
              (args forall { t => !ContainsSymbol(t, w) })) => {
        val theory = SimpleArray(args.size - 1)
        val shiftedAr = shiftTerm(ar)
        val shiftedArgs = for (t <- args) yield shiftTerm(t)
        Some((IFunApp(theory.select,
                      List(shiftedAr) ++ shiftedArgs.init) === shiftedArgs.last) &
             (IFunApp(theory.store,
                      List(shiftedAr) ++ shiftedArgs.init ++
                      List(v(depth + 1))) === w))
      }
  
      case Eq(ar, IFunApp(SimpleArray.Store(),
                          Seq(w@IVariable(`depth`), args @ _*)))
          if (!negated && !ContainsSymbol(ar, w) &&
              (args forall { t => !ContainsSymbol(t, w) })) => {
        val theory = SimpleArray(args.size - 1)
        val shiftedAr = shiftTerm(ar)
        val shiftedArgs = for (t <- args) yield shiftTerm(t)
        Some((IFunApp(theory.select,
                      List(shiftedAr) ++ shiftedArgs.init) === shiftedArgs.last) &
             (IFunApp(theory.store,
                      List(shiftedAr) ++ shiftedArgs.init ++
                      List(v(depth + 1))) === w))
      }
  
      case _ => None
    }
  }
  
  private def elimStore(expr : IExpression) : IExpression = expr match {
    case IFunApp(SimpleArray.Select(),
                 Seq(IFunApp(SimpleArray.Store(),
                             Seq(ar, storeArgs @ _*)),
                     selectArgs @ _*))
        if (storeArgs.size == selectArgs.size + 1) =>
      ite(selectArgs === storeArgs.init,
          storeArgs.last,
          IFunApp(SimpleArray(selectArgs.size).select, List(ar) ++ selectArgs))

    case IQuantified(EX, f) =>
      (for (res <- translate(f, false, 0))
       yield IQuantified(EX, IQuantified(EX, res))) getOrElse expr
    case IQuantified(ALL, f) =>
      (for (res <- translate(f, true, 0))
       yield IQuantified(ALL, IQuantified(ALL, res))) getOrElse expr
    case _ => expr
  }

  protected override def furtherSimplifications(expr : IExpression) = elimStore(expr)
}
