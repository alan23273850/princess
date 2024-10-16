import ap.Quantum
import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT.BoolADT.{True, False}
import scala.collection.mutable.ListBuffer
import IExpression._
import scala.math.{pow, asin, Pi}
import ap.theories.arrays._ // CartArray, CombArray
import scala.collection.mutable

class GroverSingleClass(val n: Int) extends Quantum(2*n) {
  import CartTheory.{arraySto, proj}
  SimpleAPI.withProver(enableAssert = debug, otherSettings = settings) { p => import p._

    val states = ListBuffer(createConstant(arrayN.sort))
    val index = createConstants(n, Sort.Bool)
    val spec = createConstant(arrayN.sort)

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
        for (i <- 0 until n) {
            if (i % 2 == 0) {
                !! (index(i) === False)
            }
            else {
                !! (index(i) === True)
            }
        }
        //////////////////////////
        val cartThs = mutable.Map(Q-1 -> new CartArray(bools(Q-1), complexSort, 3, vectorOps))
        var arrayThs = mutable.Map(Q-1 -> cartThs(Q-1).extTheories(bools(Q-1)))
        !! (proj(spec, Q-1 -> False) === arrayThs(Q-1).const(complex(0, 0, 0, 0, 0)))
        cartThs(4) = new CartArray(bools(4), complexSort, 3, vectorOps)
        arrayThs(4) = cartThs(4).extTheories(bools(4))
        !! (proj(spec, Q-1 -> True, 4 -> True) === arrayThs(4).const(complex(0, 0, 0, 0, 0)))
        cartThs(3) = new CartArray(bools(3), complexSort, 3, vectorOps)
        arrayThs(3) = cartThs(3).extTheories(bools(3))
        !! (proj(spec, Q-1 -> True, 4 -> False, 2 -> True) === arrayThs(3).const(complex(0, 0, 0, 0, 0)))

        // var subarray = s"arrayThs($n).store(List(arrayThs($n).const(complex(-32, 0, 0, 0, 17))) ++ index ++ List(complex(352, 0, 0, 0, 17)) : _*)"
        !! (proj(spec, Q-1 -> True, 4 -> False, 2 -> False) === arrayThs(3).store(List(arrayThs(3).const(complex(-32, 0, 0, 0, 17))) ++ index ++ List(complex(352, 0, 0, 0, 17)) : _*))

        // val cartThs = mutable.Map(n -> new CartArray(bools(n), complexSort, 3, vectorOps))
        // var arrayThs = mutable.Map(n -> cartThs(n).extTheories(bools(n)))
        // var subarray = s"arrayThs($n).store(List(arrayThs($n).const(complex(-32, 0, 0, 0, 17))) ++ index ++ List(complex(352, 0, 0, 0, 17)) : _*)"
        // for (i <- 2 to Q-2 by 2) {
        //     val newSize = n + i/2
        //     cartThs(newSize) = new CartArray(bools(newSize), complexSort, 3, vectorOps)
        //     arrayThs(newSize) = cartThs(newSize).extTheories(bools(newSize))
        //     subarray = s"cartThs($newSize).arraySto(arrayThs($newSize).const(complex(0, 0, 0, 0, 0)), ($i, False) -> $subarray)"
        // }
        ?? (states.last === spec)

        println(???) // valid
        // println(countGate)
        println(evalToTerm(states.last))
    }
  }
}

object GroverSingle {
    def main(args: Array[String]): Unit = {
        new GroverSingleClass(args(0).toInt).main(args)
    }
}