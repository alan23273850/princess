import ap.SimpleAPI
import ap.parser._
import ap.basetypes.IdealInt
import ap.theories.ADT
import ADT.BoolADT.{True, False}
import ap.theories.arrays._
import scala.collection.mutable.ListBuffer
import ap.parameters._
import scala.math._
import SimpleAPI.ProverStatus

class GroverSingleCompClass (val Q: Integer) extends App {

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
  def nTrue(n : Int) = (for (_ <- 0 until n) yield True).toList

  val CartTheory =
    new CartArray(bools(Q), complexSort, 1, vectorOps)
  
  val arrayN  = CartTheory.extTheories(bools(Q))
  val arrayN1 = CartTheory.extTheories(bools(Q - 1))

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

  def CZ(c : Int, t : Int, s : ITerm, CZs : ITerm) : IFormula =
    proj(CZs, c -> False)            === proj(s, c -> False) &
    proj(CZs, c -> True, t -> False) === proj(s, c -> True, t -> False) &
    proj(CZs, c -> True, t -> True)  === vec_negate(proj(s, c -> True, t -> True))

  def CCX(c : Int, d : Int, t : Int, s : ITerm, CCXs : ITerm) : IFormula =
    proj(CCXs, c -> False)            === proj(s, c -> False) &
    proj(CCXs, d -> False)            === proj(s, d -> False) &
    proj(CCXs, c -> True, d -> True, t -> False) === proj(s, c -> True, d -> True, t -> True) &
    proj(CCXs, c -> True, d -> True, t -> True)  === proj(s, c -> True, d -> True, t -> False)

  SimpleAPI.withProver(enableAssert = debug) { p => // , logging = Set(Param.LOG_TASKS
    import p._

    addTheory(CartTheory)

    val states = ListBuffer(createConstant(arrayN.sort))
    val index = createConstants(Q, Sort.Bool)
    var countH = 0

    val al = createConstant(Sort.Integer)
    val ah = createConstant(Sort.Integer)
    val aL = createConstant(Sort.Integer)
    val aH = createConstant(Sort.Integer)

    // This is one iteration of Grover's algorithm
    // with the hidden item determined by $index.
    scope {
        for (i <- 0 until Q) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! (H(i, before, after))
            countH += 1;
        }
        //
        for (i <- 0 until floor(Pi / (4 * asin(1 / pow(2, Q/2.0)))).toInt) {
            for (i <- 0 until Q) {
                val before = states.last
                states += createConstant(arrayN.sort)
                val after = states.last
                !! ((index(i) === False & X(i, before, after)) | (index(i) === True & before === after))
            }
            //
            {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            for (i <- 0 until Q) {
                !! (proj(after, i -> False) === proj(before, i -> False))
            }
            !! (sel(after, nTrue(Q) : _*) === intMult(sel(before, nTrue(Q) : _*), -1))
            }
            //
            for (i <- 0 until Q) {
                val before = states.last
                states += createConstant(arrayN.sort)
                val after = states.last
                !! ((index(i) === False & X(i, before, after)) | (index(i) === True & before === after))
            }
            for (i <- 0 until Q) {
                val before = states.last
                states += createConstant(arrayN.sort)
                val after = states.last
                !! (H(i, before, after))
                countH += 1;
            }
            for (i <- 0 until Q) {
                val before = states.last
                states += createConstant(arrayN.sort)
                val after = states.last
                !! (X(i, before, after))
            }
            //
            {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            for (i <- 0 until Q) {
                !! (proj(after, i -> False) === proj(before, i -> False))
            }
            !! (sel(after, nTrue(Q) : _*) === intMult(sel(before, nTrue(Q) : _*), -1))
            }
            //
            for (i <- 0 until Q) {
                val before = states.last
                states += createConstant(arrayN.sort)
                val after = states.last
                !! (X(i, before, after))
            }
            for (i <- 0 until Q) {
                val before = states.last
                states += createConstant(arrayN.sort)
                val after = states.last
                !! (H(i, before, after))
                countH += 1;
            }
            {
                val before = states.last
                states += createConstant(arrayN.sort)
                val after = states.last
                !! (after === vec_negate(before))
            }
        }

        !! (states.head  === sto(arrayN.const(complex(0, 0, 0, 0, 0)),
                                nFalse(Q) ++ List(complex(1, 0, 0, 0, 0)) : _*))
        !! (states.last  === sto(arrayN.const(complex(aL, 0, 0, 0, countH)),
                                index ++ List(complex(aH, 0, 0, 0, countH)) : _*))

        for (i <- 0 until Q) {
            if (i % 2 == 1)
                !! (index(i) === True)
            else
                !! (index(i) === False)
        }

        if (countH % 2 == 0)
            !! (10 * aH > 9 * (1 << (countH / 2)))
        else
            throw new RuntimeException("The number of H gates is not an even number!!!")

        val proverResult = ???
        println(proverResult) // sat
        if (proverResult == ProverStatus.Sat) {
            // println(evalToTerm(aH / (1 << (countH / 2))))
            // println(evalToTerm(aL))
            // println(evalToTerm(aH))
        }
    }
  }
}

object GroverSingleComp {
    def main(args: Array[String]): Unit = {
        new GroverSingleCompClass(args(0).toInt).main(args)
    }
}