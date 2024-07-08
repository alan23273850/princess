import ap.Quantum
import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT.BoolADT.{True, False}
import scala.collection.mutable.ListBuffer
import IExpression._

class MCXallClass(val n: Int) extends Quantum(2*n) {
  SimpleAPI.withProver(enableAssert = debug, otherSettings = settings) { p => import p._

    val states = ListBuffer(createConstant(arrayN.sort))
    // val answer = createConstants(n+1, Sort.Bool)
    val indexIn = createConstants(Q, Sort.Bool)
    val indexOut = createConstants(Q, Sort.Bool)

    scope {
        for (i <- 2 to Q-2 by 2) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! (CCX(i-2, i-1, i, before, after))
        }
        val before2 = states.last
        states += createConstant(arrayN.sort)
        val after2 = states.last
        !! (CX(Q-1, Q-2, before2, after2))
        for (i <- Q-2 to 2 by -2) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! (CCX(i-2, i-1, i, before, after))
        }
        ////////////////////////////////
        // !! (indexIn(0) === answer(0))
        var andOfControls = (indexIn(0) === True)
        if (n >= 2)
            andOfControls = andOfControls & (indexIn(1) === True)
        // !! (indexIn(1) === answer(1))
        for (i <- 2 until Q) {
            if (i % 2 == 0)
                !! (indexIn(i) === False)
            else if ((i+1) / 2 < n)
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

object MCXall {
    def main(args: Array[String]): Unit = {
        new MCXallClass(args(0).toInt).main(args)
    }
}