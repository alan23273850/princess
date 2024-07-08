import ap.Quantum
import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT.BoolADT.{True, False}
import scala.collection.mutable.ListBuffer
import IExpression._
import scala.math.{pow, asin, Pi}
import ap.theories.arrays._ // CartArray, CombArray
// import scala.reflect.runtime.currentMirror
import scala.collection.mutable

class GroverAll3storeClass(val n: Int) extends Quantum(3*n) {
  import CartTheory.{arraySto, con}
  SimpleAPI.withProver(enableAssert = debug, otherSettings = settings) { p => import p._

    val states = ListBuffer(createConstant(arrayN.sort))
    val index = createConstants(n, Sort.Bool)

    scope {
        var before = states.last
        states += createConstant(arrayN.sort)
        var after = states.last
        !! (X(Q-1, before, after))
        for (i <- 0 until n) {
            before = states.last
            states += createConstant(arrayN.sort)
            after = states.last
            !! (X(i, before, after))
        }
        before = states.last
        states += createConstant(arrayN.sort)
        after = states.last
        !! (H(n, before, after))
        for (i <- n+1 until Q by 2) {
            before = states.last
            states += createConstant(arrayN.sort)
            after = states.last
            !! (H(i, before, after))
        }
        for (_ <- 0 until (Pi / (4 * asin(1 / pow(2, n/2.0)))).toInt) {
            before = states.last
            states += createConstant(arrayN.sort)
            after = states.last
            !! (CX(0, n, before, after))
            for (i <- 1 until n) {
                before = states.last
                states += createConstant(arrayN.sort)
                after = states.last
                !! (CX(i, n+2*i-1, before, after))
            }
            assert(n >= 3)
            if (n >= 3) {
                val temp: ListBuffer[(Int, Int, Int)] = ListBuffer()
                for (t <- n+2 until Q by 2) {
                    before = states.last
                    states += createConstant(arrayN.sort)
                    after = states.last
                    !! (CCX(t-2, t-1, t, before, after))
                    temp += ((t-2, t-1, t))
                }
                // println(temp)
                ////////////////////
                before = states.last
                states += createConstant(arrayN.sort)
                after = states.last
                !! (CX(Q-2, Q-1, before, after))
                ///////////////////
                val reversedTemp = temp.reverse
                for (qubits <- reversedTemp) {
                    before = states.last
                    states += createConstant(arrayN.sort)
                    after = states.last
                    !! (CCX(qubits._1, qubits._2, qubits._3, before, after))
                }
            } else {
                // assert(n == 2)
                // sys.exit()
                // aut.Toffoli(3, 4, 5);
            }
            before = states.last
            states += createConstant(arrayN.sort)
            after = states.last
            !! (CX(0, n, before, after))
            for (i <- 1 until n) {
                before = states.last
                states += createConstant(arrayN.sort)
                after = states.last
                !! (CX(i, n+2*i-1, before, after))
            }
            before = states.last
            states += createConstant(arrayN.sort)
            after = states.last
            !! (H(n, before, after))
            for (i <- 1 until n) {
                before = states.last
                states += createConstant(arrayN.sort)
                after = states.last
                !! (H(n+2*i-1, before, after))
            }
            before = states.last
            states += createConstant(arrayN.sort)
            after = states.last
            !! (X(n, before, after))
            for (i <- 1 until n) {
                before = states.last
                states += createConstant(arrayN.sort)
                after = states.last
                !! (X(n+2*i-1, before, after))
            }
            if (n >= 3) {
                val temp: ListBuffer[(Int, Int, Int)] = ListBuffer()
                for (t <- n+2 until Q-2 by 2) {
                    before = states.last
                    states += createConstant(arrayN.sort)
                    after = states.last
                    !! (CCX(t-2, t-1, t, before, after))
                    temp += ((t-2, t-1, t))
                }
                // println(temp)
                before = states.last
                states += createConstant(arrayN.sort)
                after = states.last
                !! (CZ(3*(n-1)-1, 3*(n-1), before, after))
                val reversedTemp = temp.reverse
                for (qubits <- reversedTemp) {
                    before = states.last
                    states += createConstant(arrayN.sort)
                    after = states.last
                    !! (CCX(qubits._1, qubits._2, qubits._3, before, after))
                }
            } else {
                // assert(n == 2)
                // sys.exit()
                // # aut.CZ(3, 4);
            }
            before = states.last
            states += createConstant(arrayN.sort)
            after = states.last
            !! (X(n, before, after))
            for (i <- 1 until n) {
                before = states.last
                states += createConstant(arrayN.sort)
                after = states.last
                !! (X(n+2*i-1, before, after))
            }
            before = states.last
            states += createConstant(arrayN.sort)
            after = states.last
            !! (H(n, before, after))
            for (i <- 1 until n) {
                before = states.last
                states += createConstant(arrayN.sort)
                after = states.last
                !! (H(n+2*i-1, before, after))
            }
        }
        for (i <- 0 until n) {
            before = states.last
            states += createConstant(arrayN.sort)
            after = states.last
            !! (X(i, before, after))
        }
        before = states.last
        states += createConstant(arrayN.sort)
        after = states.last
        !! (H(Q-1, before, after))
        //////////////////////////
        !! (states.head === arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, 0)))
                           ++ index ++ nFalse(2*n) ++ List(complex(1, 0, 0, 0, 0)) : _*))
        //////////////////////////
        ?? (states.last === arraySto(con(bools(9), complex(0, 0, 0, 0, 17)), (0, index(0)) ->
            arraySto(con(bools(8), complex(0, 0, 0, 0, 17)), (0, index(1)) ->
            arraySto(con(bools(7), complex(0, 0, 0, 0, 17)), (0, index(2)) ->
            arraySto(con(bools(6), complex(0, 0, 0, 0, 17)), (5, True) ->
            arraySto(con(bools(5), complex(0, 0, 0, 0, 17)), (4, False) ->
            arraySto(con(bools(4), complex(0, 0, 0, 0, 17)), (2, False) ->
            CartTheory.extTheories(bools(3)).store(List(con(bools(3), complex(-32, 0, 0, 0, 17))) ++ index ++ List(complex(352, 0, 0, 0, 17)) : _*))))))))
        println(???) // valid
        // println(countGate)
        // println(evalToTerm(states.last))
    }
  }
}

object GroverAll3store {
    def main(args: Array[String]): Unit = {
        new GroverAll3storeClass(3).main(args)
    }
}