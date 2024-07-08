import ap.Quantum
import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT.BoolADT.{True, False}
import scala.collection.mutable.ListBuffer
import IExpression._
import scala.math.{pow, asin, Pi}
import ap.theories.arrays._ // CartArray, CombArray
import scala.collection.mutable

class GroverSingle3selectClass(val n: Int) extends Quantum(2*n) {
  import CartTheory.{arraySto, proj}
  SimpleAPI.withProver(enableAssert = debug, otherSettings = settings) { p => import p._

    val states = ListBuffer(createConstant(arrayN.sort))
    val index = createConstants(n, Sort.Bool)
    val index2 = createConstants(n, Sort.Bool)

    scope {
        var before = states.last
        states += createConstant(arrayN.sort)
        var after = states.last
        !! (X(Q-1, before, after))
        before = states.last
        states += createConstant(arrayN.sort)
        after = states.last
        !! (H(0, before, after))
        for (i <- 1 until Q by 2) {
            before = states.last
            states += createConstant(arrayN.sort)
            after = states.last
            !! (H(i, before, after))
        }
        for (_ <- 0 until (Pi / (4 * asin(1 / pow(2, n/2.0)))).toInt) {
            before = states.last
            states += createConstant(arrayN.sort)
            after = states.last
            !! (X(0, before, after))
            for (i <- 3 until Q-1 by 4) {
                before = states.last
                states += createConstant(arrayN.sort)
                after = states.last
                !! (X(i, before, after))
            }
            assert(n >= 3)
            if (n >= 3) {
                val temp: ListBuffer[(Int, Int, Int)] = ListBuffer()
                for (t <- 2 until Q by 2) {
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
            !! (X(0, before, after))
            for (i <- 3 until Q-1 by 4) {
                before = states.last
                states += createConstant(arrayN.sort)
                after = states.last
                !! (X(i, before, after))
            }
            before = states.last
            states += createConstant(arrayN.sort)
            after = states.last
            !! (H(0, before, after))
            for (i <- 1 until n) {
                before = states.last
                states += createConstant(arrayN.sort)
                after = states.last
                !! (H(2*i-1, before, after))
            }
            before = states.last
            states += createConstant(arrayN.sort)
            after = states.last
            !! (X(0, before, after))
            for (i <- 1 until n) {
                before = states.last
                states += createConstant(arrayN.sort)
                after = states.last
                !! (X(2*i-1, before, after))
            }
            if (n >= 3) {
                val temp: ListBuffer[(Int, Int, Int)] = ListBuffer()
                for (t <- 2 until Q-2 by 2) {
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
                !! (CZ(2*n-4, 2*n-3, before, after))
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
            !! (X(0, before, after))
            for (i <- 1 until n) {
                before = states.last
                states += createConstant(arrayN.sort)
                after = states.last
                !! (X(2*i-1, before, after))
            }
            before = states.last
            states += createConstant(arrayN.sort)
            after = states.last
            !! (H(0, before, after))
            for (i <- 1 until n) {
                before = states.last
                states += createConstant(arrayN.sort)
                after = states.last
                !! (H(2*i-1, before, after))
            }
        }
        before = states.last
        states += createConstant(arrayN.sort)
        after = states.last
        !! (H(Q-1, before, after))
        //////////////////////////
        !! (states.head === arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, 0)))
                                       ++ nFalse(Q) ++ List(complex(1, 0, 0, 0, 0)) : _*))
        // !! (states.head === arrayN.store(List(arrayN.store(List(arrayN.store(List(arrayN.store(List(arrayN.store(List(arrayN.store(List(arrayN.store(List(arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, 17)))
        //                                ++ List(False, False, False, False, False, True) ++ List(complex(-32, 0, 0, 0, 17)) : _*))
        //                                ++ List(False, False, False, True, False, True) ++ List(complex(-32, 0, 0, 0, 17)) : _*))
        //                                ++ List(False, True, False, False, False, True) ++ List(complex(352, 0, 0, 0, 17)) : _*))
        //                                ++ List(False, True, False, True, False, True) ++ List(complex(-32, 0, 0, 0, 17)) : _*))
        //                                ++ List(True, False, False, False, False, True) ++ List(complex(-32, 0, 0, 0, 17)) : _*))
        //                                ++ List(True, False, False, True, False, True) ++ List(complex(-32, 0, 0, 0, 17)) : _*))
        //                                ++ List(True, True, False, False, False, True) ++ List(complex(-32, 0, 0, 0, 17)) : _*))
        //                                ++ List(True, True, False, True, False, True) ++ List(complex(-32, 0, 0, 0, 17)) : _*))
        for (i <- 0 until n) {
            if (i % 2 == 0) {
                !! (index(i) === False)
            }
            else {
                !! (index(i) === True)
            }
        }
        !! (index =/= index2)
        //////////////////////////
        ?? (IFunApp(CartTheory.extTheories(bools(5)).select, List(proj(states.last, 5 -> False)) ++ createConstants(5, Sort.Bool)) === complex(0, 0, 0, 0, 17)
          & IFunApp(CartTheory.extTheories(bools(4)).select, List(proj(states.last, 5 -> True, 4 -> True)) ++ createConstants(4, Sort.Bool)) === complex(0, 0, 0, 0, 17)
          & IFunApp(CartTheory.extTheories(bools(3)).select, List(proj(states.last, 5 -> True, 4 -> False, 2 -> True)) ++ createConstants(3, Sort.Bool)) === complex(0, 0, 0, 0, 17)
          & IFunApp(CartTheory.extTheories(bools(3)).select, List(proj(states.last, 5 -> True, 4 -> False, 2 -> False)) ++ index) === complex(352, 0, 0, 0, 17)
          & IFunApp(CartTheory.extTheories(bools(3)).select, List(proj(states.last, 5 -> True, 4 -> False, 2 -> False)) ++ index2) === complex(-32, 0, 0, 0, 17))
        println(???) // valid
        // println(evalToTerm(states.last))
    }
  }
}

object GroverSingle3select {
    def main(args: Array[String]): Unit = {
        new GroverSingle3selectClass(3).main(args)
    }
}