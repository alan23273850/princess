import ap.Quantum
import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT.BoolADT.{True, False}
import scala.collection.mutable.ListBuffer
import IExpression._

class H2allClass(val n: Int) extends Quantum(n) {
  SimpleAPI.withProver(enableAssert = debug, otherSettings = settings) { p => import p._

    val states = ListBuffer(createConstant(arrayN.sort))
    val index = createConstants(Q, Sort.Bool)

    scope {
        for (i <- 0 until Q) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! (H(i, before, after))
            val before2 = states.last
            states += createConstant(arrayN.sort)
            val after2 = states.last
            !! (H(i, before2, after2))
        }

        !! (states.head === arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, 0)))
                                           ++ index ++ List(complex(1, 0, 0, 0, 0)) : _*))
        ?? (states.last === arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, countH)))
                               ++ index ++ List(complex(1<<(countH/2), 0, 0, 0, countH)) : _*))
        println(???) // valid
        // println(countGate)
        // println(evalToTerm(states.last))
    }
  }
}

object H2all {
    def main(args: Array[String]): Unit = {
        new H2allClass(args(0).toInt).main(args)
    }
}