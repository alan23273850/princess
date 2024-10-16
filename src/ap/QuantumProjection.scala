package ap;

import ap.parser._
import ap.theories.ADT.BoolADT.{True, False}
import IExpression._

class QuantumProjection(private val Q: Int, val augment2: Boolean = false) extends QuantumInterface(Q, augment2) {

  import CartTheory.{proj, sel, sto, arraySto, con}

  def X(k : Int, s : ITerm, Xs : ITerm) : IFormula = {
    countGate += 1
    return proj(Xs, k -> False) === proj(s, k -> True) &
            proj(Xs, k -> True) === proj(s, k -> False)
  }

  def Y(k : Int, s : ITerm, Ys : ITerm) : IFormula = {
    countGate += 1
    return proj(Ys, k -> False) === vec_negateN1(vec_omegaMultN1(vec_omegaMultN1(proj(s, k -> True)))) &
            proj(Ys, k -> True) === vec_omegaMultN1(vec_omegaMultN1(proj(s, k -> False)))
  }

  def Z(k : Int, s : ITerm, Zs : ITerm) : IFormula = {
    countGate += 1
    return proj(Zs, k -> False) === proj(s, k -> False) &
            proj(Zs, k -> True) === vec_negateN1(proj(s, k -> True))
  }

  def H(k : Int, s : ITerm, hs : ITerm) : IFormula = {
    countGate += 1
    countH += 1
    return proj(hs, k -> False) ===
        vec_sqrt2DivN1(vec_plusN1(proj(s, k -> False), proj(s, k -> True))) &
            proj(hs, k -> True) ===
        vec_sqrt2DivN1(vec_minusN1(proj(s, k -> False), proj(s, k -> True)))
  }

  def S(k : Int, s : ITerm, Ss : ITerm) : IFormula = {
    countGate += 1
    return proj(Ss, k -> False) === proj(s, k -> False) &
            proj(Ss, k -> True) === vec_omegaMultN1(vec_omegaMultN1(proj(s, k -> True)))
  }

  def T(k : Int, s : ITerm, Ts : ITerm) : IFormula = {
    countGate += 1
    return proj(Ts, k -> False) === proj(s, k -> False) &
            proj(Ts, k -> True) === vec_omegaMultN1(proj(s, k -> True))
  }

  def CX(c : Int, t : Int, s : ITerm, cxs : ITerm) : IFormula = {
    countGate += 1
    return proj(cxs, c -> False)            === proj(s, c -> False) &
           proj(cxs, c -> True, t -> False) === proj(s, c -> True, t -> True) &
           proj(cxs, c -> True, t -> True)  === proj(s, c -> True, t -> False)
  }

  def CZ(c : Int, t : Int, s : ITerm, CZs : ITerm) : IFormula = {
    countGate += 1
    return proj(CZs, c -> False)            === proj(s, c -> False) &
           proj(CZs, c -> True, t -> False) === proj(s, c -> True, t -> False) &
           proj(CZs, c -> True, t -> True)  === vec_negateN2(proj(s, c -> True, t -> True))
  }

  def CCX(c : Int, d : Int, t : Int, s : ITerm, CCXs : ITerm) : IFormula = {
    countGate += 1
    return proj(CCXs, c -> False)            === proj(s, c -> False) &
           proj(CCXs, d -> False)            === proj(s, d -> False) &
           proj(CCXs, c -> True, d -> True, t -> False) === proj(s, c -> True, d -> True, t -> True) &
           proj(CCXs, c -> True, d -> True, t -> True)  === proj(s, c -> True, d -> True, t -> False)
  }

  def CqZ(q : Int, s : ITerm, CqZs : ITerm) : IFormula = {
    countGate += 1
    var f : IFormula = selectN(CqZs, nTrue(q+1) : _*) === intMult(selectN(s, nTrue(q+1) : _*), -1)
    for (i <- 0 until q+1)
        f &= proj(CqZs, i -> False) === proj(s, i -> False)
    return f
  }

  def NEG(s : ITerm, NEGs : ITerm) : IFormula = {
    countGate += 1
    return NEGs === vec_negateN(s)
  }
}