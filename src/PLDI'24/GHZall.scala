import ap.Quantum
import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT.BoolADT.{True, False}
import scala.collection.mutable.ListBuffer
import IExpression._

class GHZallClass(val n: Int) extends Quantum(n) {
  SimpleAPI.withProver(enableAssert = debug, otherSettings = settings) { p => import p._

    val states = ListBuffer(createConstant(arrayN.sort))
    val index = createConstants(Q, Sort.Bool)
    val index2 = createConstants(Q, Sort.Bool)
    val index3 = createConstants(Q, Sort.Bool)

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
        !! (index2(0) === False)
        for (i <- 1 until Q) {
            !! (index2(i-1) === False & index(i) === index2(i)
               | index2(i-1) === True & index(i) =/= index2(i))
        }
        for (i <- 0 until Q) {
            !! (index2(i) =/= index3(i))
        }

        !! (states.head === arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, 0)))
                                           ++ index ++ List(complex(1, 0, 0, 0, 0)) : _*))
        ?? (index(0) === True & states.last === arrayN.store(List(arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, 1)))
                                                                                ++ index2 ++ List(complex(1, 0, 0, 0, 1)) : _*))
                                                                               ++ index3 ++ List(complex(-1, 0, 0, 0, 1)) : _*)
         | index(0) === False & states.last === arrayN.store(List(arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, 1)))
                                                                                ++ index2 ++ List(complex(1, 0, 0, 0, 1)) : _*))
                                                                                ++ index3 ++ List(complex(1, 0, 0, 0, 1)) : _*))
        println(???) // valid
        // println(countGate)
        // println(evalToTerm(states.last))
    }
  }
}

object GHZall {
    def main(args: Array[String]): Unit = {
        new GHZallClass(args(0).toInt).main(args)
    }
}