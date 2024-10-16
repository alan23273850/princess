import ap.Quantum
import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT.BoolADT.{True, False}
import scala.collection.mutable.ListBuffer
import IExpression._

class BVsingleBugClass(val N: Int, val LGQ: List[(String, List[Int])]) extends Quantum(N) {
  SimpleAPI.withProver(enableAssert = debug, otherSettings = settings) { p => import p._

    val states = ListBuffer(createConstant(arrayN.sort))
    val index = createConstants(Q, Sort.Bool)

    // This is the BV circuit with
    // the hidden string 1010...
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

object BVsingleBug {
    def main(args: Array[String]): Unit = {
        val gateCalls = QASMParser.extractGateCallsFromFile(args(0))
        new BVsingleBugClass(gateCalls._1, gateCalls._2).main(args)
    }
}