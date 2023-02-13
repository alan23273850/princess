
import ap.SimpleAPI
import ap.parser._
import ap.basetypes.IdealInt
import ap.theories.ADT
import ADT.BoolADT.{True, False}
import ap.theories.arrays._

object EPRTest extends App {

  val debug = false // change to false for much faster solving

  ap.util.Debug.enableAllAssertions(debug)

  import IExpression._

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

  val N = 20

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

  def nFalse(n : Int) = (for (_ <- 0 until n) yield False).toList

  val CartTheory =
    new CartArray(bools(N), complexSort, 2, vectorOps)
  
  val arrayN  = CartTheory.extTheories(bools(N))
  val arrayN1 = CartTheory.extTheories(bools(N - 1))
  //val arrayN2 = CartTheory.extTheories(bools(N - 2))

  import CartTheory.{proj, sel, sto}

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

  SimpleAPI.withProver(enableAssert = debug) { p =>
    import p._

    addTheory(CartTheory)

    val x0 = createConstant("x0", arrayN.sort)
    val x = createConstant("x", arrayN.sort)
    val y = createConstant("y", arrayN.sort)
    val z = createConstant("z", arrayN.sort)
    val y1 = createConstant("y1", arrayN.sort)
    val z1 = createConstant("z1", arrayN.sort)

    val comp0 = createConstant("comp0", complexSort)
    val comp1 = createConstant("comp1", complexSort)

    scope {
      !! (H(0, x, y))
      !! (CX(0, 1, y, z))
//    !! (H(0, y, z))
      !! (x0 === arrayN.const(complex(0, 0, 0, 0, 0)))
      !! (x  === sto(x0, nFalse(N) ++ List(complex(1, 0, 0, 0, 0)) : _*))
//      !! (sel(x, False :: nFalse(N - 1) : _*) === complex(1, 0, 0, 0, 0))
  //    !! (sel(x, True  :: nFalse(N - 1) : _*) === complex(2, 2, 2, 2, 1))
      !! (sel(z, False :: nFalse(N - 1) : _*) === comp0)
      !! (sel(z, True  :: nFalse(N - 1) : _*) === comp1)
      println(???) // sat
      println(evalToTerm(z))
      println(evalToTerm(comp0))
      println(evalToTerm(comp1))
    }
/*
    scope {
      val qbits = createConstants(N, Sort.Bool)

      // Assert that all k-components are initially 1
      !! (x === vec_setK1N(x0))

      // Encoding of the circuit
      !! (H(1, x, y))
      !! (H(1, y, z))
      !! (H(2, z, y1))
      !! (H(2, y1, z1))

      // Assertion: x, z coincide modulo normalization
      ?? (kInc2(kInc2(selectN(x, qbits : _*))) === selectN(z1, qbits : _*))

      println(???) // valid
    }*/


  }

}
