import ap.Quantum
import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT.BoolADT.{True, False}
import scala.collection.mutable.ListBuffer
import IExpression._

class GHZsingleBugClass(val N: Int, val LGQ: List[(String, List[Int])]) extends Quantum(N) {
  SimpleAPI.withProver(enableAssert = debug, otherSettings = settings) { p => import p._

    val states = ListBuffer(createConstant(arrayN.sort))

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

object GHZsingleBug {
    def main(args: Array[String]): Unit = {
        val gateCalls = QASMParser.extractGateCallsFromFile(args(0))
        new GHZsingleBugClass(gateCalls._1, gateCalls._2).main(args)
    }
}