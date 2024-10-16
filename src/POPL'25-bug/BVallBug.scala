import ap.Quantum
import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT.BoolADT.{True, False}
import scala.collection.mutable.ListBuffer
import IExpression._

class BVallBugClass(val N: Int, val LGQ: List[(String, List[Int])]) extends Quantum(N) {
  SimpleAPI.withProver(enableAssert = debug, otherSettings = settings) { p => import p._

    val states = ListBuffer(createConstant(arrayN.sort))
    // val answer = createConstants(n, Sort.Bool)
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

        for (i <- 0 until Q) {
            if (i % 2 == 0 && i / 2 < (Q-1) / 2) {}
                // !! (indexIn(i) === answer(i / 2))
            else
                !! (indexIn(i) === False)
        }
        for (i <- 0 until Q-1) {
            if (i % 2 == 0)
                !! (indexOut(i) === indexIn(i))
                // !! (indexOut(i) === answer(i / 2))
            else
                !! (indexOut(i) === indexOut(i-1))
        }
        !! (indexOut(Q-1) === True)

        !! (states.head === arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, 0)))
                                         ++ indexIn ++ List(complex(1, 0, 0, 0, 0)) : _*))
        ?? (states.last === arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, countH)))
                                     ++ indexOut ++ List(complex(1<<(countH/2), 0, 0, 0, countH)) : _*))

        println(???) // valid
        // println(countGate)
        println(evalToTerm(states.last))
    }
  }
}

object BVallBug {
    def main(args: Array[String]): Unit = {
        val gateCalls = QASMParser.extractGateCallsFromFile(args(0))
        new BVallBugClass(gateCalls._1, gateCalls._2).main(args)
    }
}