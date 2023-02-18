import ap.Quantum
import ap.SimpleAPI
import ap.parser._
import scala.collection.mutable.ListBuffer
import IExpression._

object BV1bug extends Quantum(1) {
  SimpleAPI.withProver(enableAssert = debug) { p => import p._

    val states = ListBuffer(createConstant(arrayN.sort))
    val index = createConstants(1, Sort.Bool)

    // This is the BV circuit with
    // the hidden string 1010...
    scope {
        for (i <- 0 until 1) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! (H(i, before, after))
        }
        for (i <- 0 until 1 by 2) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! (Y(i, before, after))
        }
        for (i <- 0 until 1) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! (H(i, before, after))
        }

        !! (states.head  === arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, 0)))
                                        ++ nFalse(1) ++ List(complex(1, 0, 0, 0, 0)) : _*))
        !! (b(selectN(states.last, index : _*)) =/= 0 |
            c(selectN(states.last, index : _*)) =/= 0 |
            d(selectN(states.last, index : _*)) =/= 0)

        println(???) // sat
        // println(evalToTerm(states.last))
    }
  }
}