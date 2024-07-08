import ap.Quantum
import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT.BoolADT.{True, False}
import scala.collection.mutable.ListBuffer
import IExpression._

class BVsingleClass(val n: Int) extends Quantum(n+1) {
  SimpleAPI.withProver(enableAssert = debug, otherSettings = settings) { p => import p._

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
        val before = states.last
        states += createConstant(arrayN.sort)
        val after = states.last
        !! (Z(Q-1, before, after))
        for (i <- 0 until Q-1 by 2) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! (CX(i, Q-1, before, after))
        }
        for (i <- 0 until Q) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! (H(i, before, after))
        }

        !! (states.head === arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, 0)))
                                       ++ nFalse(Q) ++ List(complex(1, 0, 0, 0, 0)) : _*))
        for (i <- 0 until Q-1) {
            if (i % 2 == 0) {
                !! (index(i) === True)
            }
            else {
                !! (index(i) === False)
            }
        }
        !! (index(Q-1) === True)
        ?? (states.last === arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, 2*Q)))
                                           ++ index ++ List(complex(1<<Q, 0, 0, 0, 2*Q)) : _*))

        println(???) // valid
        // println(countGate)
        // println(evalToTerm(states.last))
    }
  }
}

object BVsingle {
    def main(args: Array[String]): Unit = {
        new BVsingleClass(args(0).toInt).main(args)
    }
}