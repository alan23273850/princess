package ap;

import ap.parser._
import ap.theories.ADT.BoolADT.{True, False}
import IExpression._

class QuantumArrayStore(private val Q: Int) extends QuantumInterface(Q) {

  import CartTheory.{proj, sel, sto, arraySto, con}

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