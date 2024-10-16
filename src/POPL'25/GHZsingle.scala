import ap.Quantum
import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT.BoolADT.{True, False}
import scala.collection.mutable.ListBuffer
import IExpression._

class GHZsingleClass(val n: Int) extends Quantum(n) {
  SimpleAPI.withProver(enableAssert = debug, otherSettings = settings) { p => import p._

    val states = ListBuffer(createConstant(arrayN.sort))

    scope {
        val before = states.last
        states += createConstant(arrayN.sort)
        val after = states.last
        !! (H(0, before, after))
        for (i <- 1 until Q) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! (CX(i-1, i, before, after))
        }

        !! (states.head === arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, 0)))
                                       ++ nFalse(Q) ++ List(complex(1, 0, 0, 0, 0)) : _*))
        ?? (states.last === arrayN.store(List(arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, 1)))
                                           ++ nFalse(Q) ++ List(complex(1, 0, 0, 0, 1)) : _*))
                                            ++ nTrue(Q) ++ List(complex(1, 0, 0, 0, 1)) : _*))
        println(???) // valid
        // println(countGate)
        println(evalToTerm(states.last))
    }
  }
}

object GHZsingle {
    def main(args: Array[String]): Unit = {
        new GHZsingleClass(args(0).toInt).main(args)
    }
}