package ap;

import ap.parser._
import ap.basetypes.IdealInt
import ap.theories.ADT
import ADT.BoolADT.{True, False}
import ap.theories.arrays._
import IExpression._

class Quantum(val Q: Int) extends App {

  var countGate = 0
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
  import CartTheory.{proj, sel, sto, arraySto, con}
  
  val arrayN  = CartTheory.extTheories(bools(Q))

  val arrayNComb = CartTheory.combTheories(bools(Q))
  val Seq(vec_plusN, vec_minusN,
          vec_omegaMultN, vec_negateN,
          vec_sqrt2DivN, vec_setK1N) = arrayNComb.combinators
  val arrayN1Comb = CartTheory.combTheories(bools(Q - 1))
  val Seq(vec_plusN1, vec_minusN1,
          vec_omegaMultN1, vec_negateN1,
          vec_sqrt2DivN1, vec_setK1N1) = arrayN1Comb.combinators

  def selectN(ar : ITerm, indexes : ITerm*) : ITerm =
    IFunApp(arrayN.select, List(ar) ++ indexes)

  def X(k : Int, s : ITerm, Xs : ITerm) : IFormula = {
    countGate += 1
    return Xs === arraySto(arraySto(s,
        (k, False) -> proj(s, k -> True)),
        (k, True)  -> proj(s, k -> False))
  }

  def Y(k : Int, s : ITerm, Ys : ITerm) : IFormula = {
    countGate += 1
    return Ys === arraySto(arraySto(s,
        (k, False) -> vec_negateN1(vec_omegaMultN1(vec_omegaMultN1(proj(s, k -> True))))),
        (k, True)  -> vec_omegaMultN1(vec_omegaMultN1(proj(s, k -> False))))
  }

  def Z(k : Int, s : ITerm, Zs : ITerm) : IFormula = {
    countGate += 1
    return Zs === arraySto(s,
        (k, True) -> vec_negateN1(proj(s, k -> True)))
  }

  def H(k : Int, s : ITerm, Hs : ITerm) : IFormula = {
    countGate += 1
    return Hs === arraySto(arraySto(s,
        (k, False) -> vec_sqrt2DivN1(vec_plusN1(proj(s, k -> False), proj(s, k -> True)))),
		(k, True)  -> vec_sqrt2DivN1(vec_minusN1(proj(s, k -> False), proj(s, k -> True))))
  }

  def S(k : Int, s : ITerm, Ss : ITerm) : IFormula = {
    countGate += 1
    return Ss === arraySto(s,
        (k -> True) -> vec_omegaMultN1(vec_omegaMultN1(proj(s, k -> True))))
  }

  def T(k : Int, s : ITerm, Ts : ITerm) : IFormula = {
    countGate += 1
    return Ts === arraySto(s,
        (k -> True) -> vec_omegaMultN1(proj(s, k -> True)))
  }

  def CX(c : Int, t : Int, s : ITerm, cxs : ITerm) : IFormula = {
    // countGate += 1
    return arrayN.sort.ex((temp) => (
        X(t, s, temp) &
        cxs === arraySto(s , (c, True)  -> proj(temp, c -> True))))
  }

  def CZ(c : Int, t : Int, s : ITerm, CZs : ITerm) : IFormula = {
    // countGate += 1
    return arrayN.sort.ex((temp) => (
        Z(t, s, temp) &
        CZs === arraySto(s , (c, True)  -> proj(temp, c -> True))))
  }

  def CCX(c : Int, d : Int, t : Int, s : ITerm, CCXs : ITerm) : IFormula = {
    // countGate += 1
    return arrayN.sort.ex((temp) => (
        CX(d, t, s, temp) &
        CCXs === arraySto(s , (c, True)  -> proj(temp, c -> True))))
  }

  def CqZ(q : Int, s : ITerm, CqZs : ITerm) : IFormula = {
    // countGate += 1
    if (q == 0) return Z(q, s, CqZs)
    return arrayN.sort.ex((temp) => (
        CqZ(q-1, s, temp) &
        CqZs === arraySto(s , (q, True)  -> proj(temp, q -> True))))
  }

  def NEG(s : ITerm, NEGs : ITerm) : IFormula = {
    countGate += 1
    return NEGs === vec_negateN(s)
  }
}