import ap.Quantum
import ap.SimpleAPI
import ap.parser._
import scala.collection.mutable.ListBuffer
import IExpression._

class BVClass(val n: Int) extends Quantum(n) {
  SimpleAPI.withProver(enableAssert = debug) { p => import p._

    val states = ListBuffer(createConstant(arrayN.sort))
    val index = createConstants(Q, Sort.Bool)

    // This is the BV circuit with
    // the hidden string 1010...
    scope {
        for (i <- 0 until Q) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! (H(i, before, after))
        }
        for (i <- 0 until Q by 2) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! (Z(i, before, after))
        }
        for (i <- 0 until Q) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! (H(i, before, after))
        }

        !! (states.head  === arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, 0)))
                                        ++ nFalse(Q) ++ List(complex(1, 0, 0, 0, 0)) : _*))
        !! (b(selectN(states.last, index : _*)) =/= 0 |
            c(selectN(states.last, index : _*)) =/= 0 |
            d(selectN(states.last, index : _*)) =/= 0)

        println(???) // UNsat
        // println(evalToTerm(states.last))
    }
  }
}

object BVTest {
    def main(args: Array[String]): Unit = {
        new BVClass(args(0).toInt).main(args)
    }
}