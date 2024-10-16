import ap.Quantum
import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT.BoolADT
import ap.theories.ADT.BoolADT.{True, False}
import scala.collection.mutable.ListBuffer
import IExpression._
import scala.math.{pow, asin, Pi}
import ap.theories.arrays._ // CartArray, CombArray
// import scala.reflect.runtime.currentMirror
import scala.collection.mutable.ArrayBuffer

class GroverAllBugClass(val N: Int, val LGQ: List[(String, List[Int])]) extends Quantum(N, true) {
  import CartTheory.{arraySto, con, proj}
  SimpleAPI.withProver(enableAssert = debug, otherSettings = settings) { p => import p._

    val n = N / 3
    val states = ListBuffer(createConstant(arrayN.sort))
    val index = createConstants(n, Sort.Bool)
    val indexNot = createConstants(n, Sort.Bool)

    val aH = Map(3 -> (11, 7), 6 -> (133988401, 54))//, 7 -> (12412280691169, 87), 8 -> (75555863006653472909761, 152))
    val aL = Map(3 -> (-1, 7), 6 -> (-988079, 54))//, 7 -> (73054448161, 87), 8 -> (34433006489313897025, 152))

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
        //////////////////////////
        !! (states.head === arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, 0)))
                                       ++ index ++ nFalse(2*n) ++ List(complex(1, 0, 0, 0, 0)) : _*))
        //////////////////////////
        var aH_n = 0 //BigInt(0)
        if (aH(n)._2 <= countH) {
            aH_n = aH(n)._1/*.asInstanceOf[BigInt]*/ << ((countH - aH(n)._2) / 2)
        } else {
            aH_n = aH(n)._1/*.asInstanceOf[BigInt]*/ >> ((aH(n)._2 - countH) / 2)
        }
        var aL_n = 0 //BigInt(0)
        if (aL(n)._2 <= countH) {
            aL_n = aL(n)._1/*.asInstanceOf[BigInt]*/ << ((countH - aL(n)._2) / 2)
        } else {
            aL_n = aL(n)._1/*.asInstanceOf[BigInt]*/ >> ((aL(n)._2 - countH) / 2)
        }
        // ?? (proj(states.last, 8 -> False) === con(bools(8), complex(0, 0, 0, 0, countH))
        //   & proj(states.last, 8 -> True, 7 -> True) === con(bools(7), complex(0, 0, 0, 0, countH))
        //   & proj(states.last, 8 -> True, 7 -> False, 5 -> True) === con(bools(6), complex(0, 0, 0, 0, countH))
        //   & proj(states.last, 8 -> True, 7 -> False, 5 -> False, 2 -> indexNot(2)) === con(bools(5), complex(0, 0, 0, 0, countH))
        //   & proj(states.last, 8 -> True, 7 -> False, 5 -> False, 2 -> index(2), 1 -> indexNot(1)) === con(bools(4), complex(0, 0, 0, 0, countH))
        //   & proj(states.last, 8 -> True, 7 -> False, 5 -> False, 2 -> index(2), 1 -> index(1), 0 -> indexNot(0)) === con(bools(3), complex(0, 0, 0, 0, countH))
        //   & proj(states.last, 8 -> True, 7 -> False, 5 -> False, 2 -> index(2), 1 -> index(1), 0 -> index(0))
        //     === CartTheory.extTheories(bools(3)).store(List(con(bools(3), complex(-32, 0, 0, 0, countH))) ++ index ++ List(complex(352, 0, 0, 0, countH)) : _*))
        for (i <- 0 until n) {
            !! (index(i) =/= indexNot(i))
        }
        var seqOfTuples = ArrayBuffer[(Int, ITerm)]((N-1, False))
        var property = proj(states.last, seqOfTuples: _*) === con(bools(N-1), complex(0, 0, 0, 0, countH))
        seqOfTuples = ArrayBuffer[(Int, ITerm)]((N-1, True), (N-2, True))
        property &= proj(states.last, seqOfTuples: _*) === con(bools(N-2), complex(0, 0, 0, 0, countH))
        for (i <- 0 until n-2) {
            seqOfTuples(seqOfTuples.length - 1) = (seqOfTuples.last._1, False)
            seqOfTuples += ((seqOfTuples.last._1 - 2, True))
            property &= proj(states.last, seqOfTuples: _*) === con(bools(N-3-i), complex(0, 0, 0, 0, countH))
        }
        seqOfTuples(seqOfTuples.length - 1) = (seqOfTuples.last._1, False)
        seqOfTuples += ((n-1, indexNot(n-1)))
        property &= proj(states.last, seqOfTuples: _*) === con(bools(2*n-1), complex(0, 0, 0, 0, countH))
        for (i <- n-2 to 0 by -1) {
            seqOfTuples(seqOfTuples.length - 1) = (seqOfTuples.last._1, index(i+1))
            seqOfTuples += ((i, indexNot(i)))
            property &= proj(states.last, seqOfTuples: _*) === con(bools(i+n), complex(0, 0, 0, 0, countH))
        }
        seqOfTuples(seqOfTuples.length - 1) = (seqOfTuples.last._1, index(0))
        property &= proj(states.last, seqOfTuples: _*) === CartTheory.extTheories(bools(n)).store(List(con(bools(n), complex(aL_n, 0, 0, 0, countH))) ++ index ++ List(complex(aH_n, 0, 0, 0, countH)) : _*)
        ?? (property)
        println(???) // valid
        // println(countGate)
        // println(evalToTerm(states.last))
    }
  }
}

object GroverAllBug {
    def main(args: Array[String]): Unit = {
        val gateCalls = QASMParser.extractGateCallsFromFile(args(0))
        new GroverAllBugClass(gateCalls._1, gateCalls._2).main(args)
    }
}
