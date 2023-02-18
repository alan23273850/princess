import ap.Quantum
import ap.SimpleAPI
import ap.parser._
import scala.collection.mutable.ListBuffer
import IExpression._

object H2 extends Quantum(1) {
    SimpleAPI.withProver(enableAssert = debug) { p => import p._

    val states = ListBuffer(createConstant(arrayN.sort))
    val vars = (for (i <- 0 until 8) yield createConstant(Sort.Integer)).toArray

    scope {
        !! (states.head  === arrayN.store(List(arrayN.const(complex(vars(0), vars(1), vars(2), vars(3), 0)))
                                        ++ nTrue(1)
                                        ++ List(complex(vars(4), vars(5), vars(6), vars(7), 0)) : _*))

        for (i <- 0 until 2) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last    
            !! (H(0, before, after))
        }

        !! ((2 * vars(0) =/= a(selectN(states.last, nFalse(1) : _*)))
            | (2 * vars(1) =/= b(selectN(states.last, nFalse(1) : _*)))
            | (2 * vars(2) =/= c(selectN(states.last, nFalse(1) : _*)))
            | (2 * vars(3) =/= d(selectN(states.last, nFalse(1) : _*)))
            | (2 * vars(4) =/= a(selectN(states.last, nTrue(1) : _*)))
            | (2 * vars(5) =/= b(selectN(states.last, nTrue(1) : _*)))
            | (2 * vars(6) =/= c(selectN(states.last, nTrue(1) : _*)))
            | (2 * vars(7) =/= d(selectN(states.last, nTrue(1) : _*))))

        println(???)
    }
  }
}