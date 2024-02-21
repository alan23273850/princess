import ap.Quantum
import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT.BoolADT.{True, False}
import scala.collection.mutable.ListBuffer
import IExpression._

class BVallClass(val n: Int) extends Quantum(2*n+1) {
  SimpleAPI.withProver(enableAssert = debug, otherSettings = settings) { p => import p._

    val states = ListBuffer(createConstant(arrayN.sort))
    // val answer = createConstants(n, Sort.Bool)
    val indexIn = createConstants(Q, Sort.Bool)
    val indexOut = createConstants(Q, Sort.Bool)

    scope {
        for (i <- 1 until Q-1 by 2) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! (H(i, before, after))
        }
        val before = states.last
        states += createConstant(arrayN.sort)
        val after = states.last
        !! (H(Q-1, before, after))
        val before2 = states.last
        states += createConstant(arrayN.sort)
        val after2 = states.last
        !! (Z(Q-1, before2, after2))
        for (i <- 1 until Q-1 by 2) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! (CCX(i-1, i, Q-1, before, after))
        }
        for (i <- 1 until Q-1 by 2) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! (H(i, before, after))
        }
        val before3 = states.last
        states += createConstant(arrayN.sort)
        val after3 = states.last
        !! (H(Q-1, before3, after3))

        for (i <- 0 until Q) {
            if (i % 2 == 0 && i / 2 < n) {}
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

object BVall {
    def main(args: Array[String]): Unit = {
        new BVallClass(args(0).toInt).main(args)
    }
}