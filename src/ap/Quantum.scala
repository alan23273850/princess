package ap;

import ap.parser._
import ap.basetypes.IdealInt
import ap.theories.ADT
import ADT.BoolADT.{True, False}
import ap.theories.arrays._
import IExpression._

class Quantum(val Q: Int) extends App {

  val debug = false // change to false for much faster solving

  ap.util.Debug.enableAllAssertions(debug)

  val (complexSort, complex, Seq(a, b, c, d, k)) =
    ADT.createRecordType("Complex", List(("a", Sort.Integer),
                                         ("b", Sort.Integer),
                                         ("c", Sort.Integer),
                                         ("d", Sort.Integer),
                                         ("k", Sort.Nat)))

  // This just assumes (and does not verify) that the k's are consistent
  def complexPlus(s : ITerm, t : ITerm) : ITerm =
    complex(a(s) + a(t), b(s) + b(t), c(s) + c(t), d(s) + d(t), k(s))

  // This just assumes (and does not verify) that the k's are consistent
  def complexMinus(s : ITerm, t : ITerm) : ITerm =
    complex(a(s) - a(t), b(s) - b(t), c(s) - c(t), d(s) - d(t), k(s))

  def omegaMult(s : ITerm) : ITerm =
    complex(-d(s), a(s), b(s), c(s), k(s))

  def intMult(s : ITerm, n : IdealInt) : ITerm =
    complex(a(s) * n, b(s) * n, c(s) * n, d(s) * n, k(s))

  def sqrt2Div(s : ITerm) : ITerm =
    complex(a(s), b(s), c(s), d(s), k(s) + 1)

  def kInc2(s : ITerm) : ITerm =
    complex(a(s) * 2, b(s) * 2, c(s) * 2, d(s) * 2, k(s) + 2)

  def setK1(s : ITerm) : ITerm =
    complex(a(s), b(s), c(s), d(s), 1)

  val vectorOps = Vector(
    CombArray.CombinatorSpec("vec_plus", List(0, 0), 0,
                             v(2, complexSort) === complexPlus(v(0, complexSort), v(1, complexSort))),
    CombArray.CombinatorSpec("vec_minus", List(0, 0), 0,
                             v(2, complexSort) === complexMinus(v(0, complexSort), v(1, complexSort))),
    CombArray.CombinatorSpec("vec_omegaMult", List(0), 0,
                             v(1, complexSort) === omegaMult(v(0, complexSort))),
    CombArray.CombinatorSpec("vec_negate", List(0), 0,
                             v(1, complexSort) === intMult(v(0, complexSort), -1)),
    CombArray.CombinatorSpec("vec_sqrt2Div", List(0), 0,
                             v(1, complexSort) === sqrt2Div(v(0, complexSort))),
    CombArray.CombinatorSpec("vec_setK1", List(0), 0,
                             v(1, complexSort) === setK1(v(0, complexSort)))
  )

  def bools(n : Int) = for (_ <- 0 until n) yield Sort.Bool
  def nTrue(n : Int) = (for (_ <- 0 until n) yield True).toList
  def nFalse(n : Int) = (for (_ <- 0 until n) yield False).toList

  val CartTheory =
    new CartArray(bools(Q), complexSort, 3, vectorOps)
  import CartTheory.{proj, sel, sto}
  
  val arrayN  = CartTheory.extTheories(bools(Q))

  val Seq(vec_plus, vec_minus,
          vec_omegaMult, vec_negate,
          vec_sqrt2Div, vec_setK1) = CartTheory.combinators

  def selectN(ar : ITerm, indexes : ITerm*) : ITerm =
    IFunApp(arrayN.select, List(ar) ++ indexes)

  def X(k : Int, s : ITerm, Xs : ITerm) : IFormula =
    proj(Xs, k -> False) === proj(s, k -> True) &
    proj(Xs, k -> True) === proj(s, k -> False)

  def Y(k : Int, s : ITerm, Ys : ITerm) : IFormula =
    proj(Ys, k -> False) === vec_negate(vec_omegaMult(vec_omegaMult(proj(s, k -> True)))) &
    proj(Ys, k -> True) === vec_omegaMult(vec_omegaMult(proj(s, k -> False)))

  def Z(k : Int, s : ITerm, Zs : ITerm) : IFormula =
    proj(Zs, k -> False) === proj(s, k -> False) &
    proj(Zs, k -> True) === vec_negate(proj(s, k -> True))

  def H(k : Int, s : ITerm, hs : ITerm) : IFormula =
    proj(hs, k -> False) ===
      vec_sqrt2Div(vec_plus(proj(s, k -> False), proj(s, k -> True))) &
    proj(hs, k -> True) ===
      vec_sqrt2Div(vec_minus(proj(s, k -> False), proj(s, k -> True)))

  def S(k : Int, s : ITerm, Ss : ITerm) : IFormula =
    proj(Ss, k -> False) === proj(s, k -> False) &
    proj(Ss, k -> True) === vec_omegaMult(vec_omegaMult(proj(s, k -> True)))

  def T(k : Int, s : ITerm, Ts : ITerm) : IFormula =
    proj(Ts, k -> False) === proj(s, k -> False) &
    proj(Ts, k -> True) === vec_omegaMult(proj(s, k -> True))

  def CX(c : Int, t : Int, s : ITerm, cxs : ITerm) : IFormula =
    proj(cxs, c -> False)            === proj(s, c -> False) &
    proj(cxs, c -> True, t -> False) === proj(s, c -> True, t -> True) &
    proj(cxs, c -> True, t -> True)  === proj(s, c -> True, t -> False)

  def CZ(c : Int, t : Int, s : ITerm, CZs : ITerm) : IFormula =
    proj(CZs, c -> False)            === proj(s, c -> False) &
    proj(CZs, c -> True, t -> False) === proj(s, c -> True, t -> False) &
    proj(CZs, c -> True, t -> True)  === vec_negate(proj(s, c -> True, t -> True))

  def CCX(c : Int, d : Int, t : Int, s : ITerm, CCXs : ITerm) : IFormula =
    proj(CCXs, c -> False)            === proj(s, c -> False) &
    proj(CCXs, d -> False)            === proj(s, d -> False) &
    proj(CCXs, c -> True, d -> True, t -> False) === proj(s, c -> True, d -> True, t -> True) &
    proj(CCXs, c -> True, d -> True, t -> True)  === proj(s, c -> True, d -> True, t -> False)

  def CqZ(q : Int, s : ITerm, CqZs : ITerm) : IFormula = {
    var f : IFormula = selectN(CqZs, nTrue(q) : _*) === intMult(selectN(s, nTrue(q) : _*), -1)
    for (i <- 0 until q)
        f &= proj(CqZs, i -> False) === proj(s, i -> False)
    return f
  }
}