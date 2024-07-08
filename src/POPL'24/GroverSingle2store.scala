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

class GroverSingle2storeClass(val n: Int) extends Quantum(3) {
  import CartTheory.{arraySto, con, proj}
  SimpleAPI.withProver(enableAssert = debug, otherSettings = settings) { p => import p._

    val states = ListBuffer(createConstant(arrayN.sort))
    val index = createConstants(n, Sort.Bool)

    scope {
        var before = states.last
        states += createConstant(arrayN.sort)
        var after = states.last
        !! (X(Q-1, before, after))
        for (i <- 0 until Q) {
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
            before = states.last
            states += createConstant(arrayN.sort)
            after = states.last
            !! (CCX(0, 1, 2, before, after))
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
            before = states.last
            states += createConstant(arrayN.sort)
            after = states.last
            !! (CZ(0, 1, before, after))
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
        ?? (states.last === arraySto(con(bools(3), complex(0, 0, 0, 0, countH)), (2, True) ->
                            CartTheory.extTheories(bools(2)).store(List(con(bools(2), complex(0, 0, 0, 0, countH))) ++ index ++ List(complex(-1<<(countH/2), 0, 0, 0, countH)) : _*)))
        println(???) // valid
        // println(countGate)
        println(evalToTerm(states.last))
    }
  }
}

object GroverSingle2store {
    def main(args: Array[String]): Unit = {
        new GroverSingle2storeClass(2).main(args)
    }
}