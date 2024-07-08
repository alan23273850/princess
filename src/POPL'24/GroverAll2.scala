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

class GroverAll2Class(val n: Int) extends Quantum(3*n-1) {
  import CartTheory.arraySto
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
        for (i <- n until Q) {
            before = states.last
            states += createConstant(arrayN.sort)
            after = states.last
            !! (H(i, before, after))
        }
        for (_ <- 0 until (Pi / (4 * asin(1 / pow(2, n/2.0)))).toInt) {
            for (i <- 0 until n) {
                before = states.last
                states += createConstant(arrayN.sort)
                after = states.last
                !! (CX(i, n+i, before, after))
            }
            before = states.last
            states += createConstant(arrayN.sort)
            after = states.last
            !! (CCX(2, 3, 4, before, after))
            for (i <- 0 until n) {
                before = states.last
                states += createConstant(arrayN.sort)
                after = states.last
                !! (CX(i, n+i, before, after))
            }
            for (i <- n to Q-1) {
                before = states.last
                states += createConstant(arrayN.sort)
                after = states.last
                !! (H(i, before, after))
            }
            for (i <- n to Q-1) {
                before = states.last
                states += createConstant(arrayN.sort)
                after = states.last
                !! (X(i, before, after))
            }
            before = states.last
            states += createConstant(arrayN.sort)
            after = states.last
            !! (CZ(2, 3, before, after))
            for (i <- n to Q-1) {
                before = states.last
                states += createConstant(arrayN.sort)
                after = states.last
                !! (X(i, before, after))
            }
            for (i <- n to Q-1) {
                before = states.last
                states += createConstant(arrayN.sort)
                after = states.last
                !! (H(i, before, after))
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
                                       ++ index ++ nFalse(2*n-1) ++ List(complex(1, 0, 0, 0, 0)) : _*))
        //////////////////////////
        ?? (states.last === arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, countH))) ++ List(False, False, False, False, True) ++ List(complex(-1<<(countH/2), 0, 0, 0, countH)) : _*)
        | states.last === arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, countH))) ++ List(False, True, False, True, True) ++ List(complex(-1<<(countH/2), 0, 0, 0, countH)) : _*)
        | states.last === arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, countH))) ++ List(True, False, True, False, True) ++ List(complex(-1<<(countH/2), 0, 0, 0, countH)) : _*)
        | states.last === arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, countH))) ++ List(True, True, True, True, True) ++ List(complex(-1<<(countH/2), 0, 0, 0, countH)) : _*))
        println(???) // valid
        // println(countGate)
        // println(evalToTerm(states.last))
    }
  }
}

object GroverAll2 {
    def main(args: Array[String]): Unit = {
        new GroverAll2Class(2).main(args)
    }
}