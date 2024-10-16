import ap.Quantum
import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT.BoolADT.{True, False}
import scala.collection.mutable.ListBuffer
import IExpression._

class MCXallBugClass(val N: Int, val LGQ: List[(String, List[Int])]) extends Quantum(N) {
  SimpleAPI.withProver(enableAssert = debug, otherSettings = settings) { p => import p._

    val states = ListBuffer(createConstant(arrayN.sort))
    // val answer = createConstants(n+1, Sort.Bool)
    val indexIn = createConstants(Q, Sort.Bool)
    val indexOut = createConstants(Q, Sort.Bool)

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
        ////////////////////////////////
        // !! (indexIn(0) === answer(0))
        var andOfControls = (indexIn(0) === True)
        if (Q/2 >= 2)
            andOfControls = andOfControls & (indexIn(1) === True)
        // !! (indexIn(1) === answer(1))
        for (i <- 2 until Q) {
            if (i % 2 == 0)
                !! (indexIn(i) === False)
            else if ((i+1) / 2 < Q/2)
                andOfControls = andOfControls & (indexIn(i) === True)
                // !! (indexIn(i) === answer((i+1) / 2))
        }
        for (i <- 0 until Q-1) {
            !! (indexIn(i) === indexOut(i))
        }
        !! (andOfControls <=> (indexOut(Q-1) =/= indexIn(Q-1)))

        !! (states.head === arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, 0)))
                                         ++ indexIn ++ List(complex(1, 0, 0, 0, 0)) : _*))
        ?? (states.last === arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, 0)))
                                        ++ indexOut ++ List(complex(1, 0, 0, 0, 0)) : _*))

        println(???) // valid
        // println(countGate)
        println(evalToTerm(states.last))
    }
  }
}

object MCXallBug {
    def main(args: Array[String]): Unit = {
        val gateCalls = QASMParser.extractGateCallsFromFile(args(0))
        new MCXallBugClass(gateCalls._1, gateCalls._2).main(args)
    }
}