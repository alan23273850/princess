import ap.Quantum
import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT.BoolADT.{True, False}
import scala.collection.mutable.ListBuffer
import IExpression._

class GHZallBugClass(val N: Int, val LGQ: List[(String, List[Int])]) extends Quantum(N) {
  SimpleAPI.withProver(enableAssert = debug, otherSettings = settings) { p => import p._

    val states = ListBuffer(createConstant(arrayN.sort))
    val index = createConstants(Q, Sort.Bool)
    val index2 = createConstants(Q, Sort.Bool)
    val index3 = createConstants(Q, Sort.Bool)

    scope {
        for (GQ <- LGQ) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            GQ._1 match {
                case "x" => !! (X(GQ._2.apply(0), before, after))
                case "y" => !! (Y(GQ._2.apply(0), before, after))
                case "z" => !! (Z(GQ._2.apply(0), before, after))
                case "h" => !! (H(GQ._2.apply(0), before, after))
                case "s" => !! (S(GQ._2.apply(0), before, after))
                case "t" => !! (T(GQ._2.apply(0), before, after))
                case "cx" => !! (CX(GQ._2.apply(0), GQ._2.apply(1), before, after))
                case "cz" => !! (CZ(GQ._2.apply(0), GQ._2.apply(1), before, after))
                case "ccx" => !! (CCX(GQ._2.apply(0), GQ._2.apply(1), GQ._2.apply(2), before, after))
                case _ => throw new RuntimeException("Unimplemented Gate!!!")
            }
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

object GHZallBug {
    def main(args: Array[String]): Unit = {
        val gateCalls = QASMParser.extractGateCallsFromFile(args(0))
        new GHZallBugClass(gateCalls._1, gateCalls._2).main(args)
    }
}