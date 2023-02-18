import ap.Quantum
import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT.BoolADT.{True, False}
import scala.collection.mutable.ListBuffer
import scala.math._
import IExpression._
import SimpleAPI.ProverStatus

class GroverAllCompClass(val n: Int) extends Quantum(n) {
  SimpleAPI.withProver(enableAssert = debug) { p => import p._

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
                !! (CqZ(Q, before, after))
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
                !! (CqZ(Q, before, after))
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

        !! (states.head  === arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, 0)))
                                        ++ nFalse(Q) ++ List(complex(1, 0, 0, 0, 0)) : _*))
        !! (states.last  === arrayN.store(List(arrayN.const(complex(aL, 0, 0, 0, countH)))
                                        ++ index ++ List(complex(aH, 0, 0, 0, countH)) : _*))

        if (countH % 2 == 0)
            !! (! (100 * aH > 95 * (1 << (countH / 2))))
        else
            throw new RuntimeException("The number of H gates is not an even number!!!")

        val proverResult = ???
        println(proverResult) // UNsat
        if (proverResult == ProverStatus.Sat) {
            // println(evalToTerm(aH / (1 << (countH / 2))))
            // println(evalToTerm(aL))
            // println(evalToTerm(aH))
        }
    }
  }
}

object GroverAllComp {
    def main(args: Array[String]): Unit = {
        new GroverAllCompClass(args(0).toInt).main(args)
    }
}