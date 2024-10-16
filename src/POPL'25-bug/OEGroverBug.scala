import ap.Quantum
import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT.BoolADT.{True, False}
import scala.collection.mutable.ListBuffer
import IExpression._
import scala.math.{pow, asin, Pi, BigInt}
import ap.theories.arrays._ // CartArray, CombArray
// import scala.reflect.runtime.currentMirror
import scala.collection.mutable.ArrayBuffer
import scala.collection.immutable.Map

class OEGroverBugClass(val N: Int, val LGQ: List[(String, List[Int])]) extends Quantum(N) {
  import CartTheory.arraySto
  SimpleAPI.withProver(enableAssert = debug, otherSettings = settings) { p => import p._

    val states = ListBuffer(createConstant(arrayN.sort))
    val aH = createConstant(Sort.Integer)
    val aL = createConstant(Sort.Integer)
    val bH = createConstant(Sort.Integer)
    val bL = createConstant(Sort.Integer)

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
        /////////////////////////////
        val n = (N+1) / 2
        !! (aL > 0)
        !! (aH > 0)
        !! (((1 << n) - 1) * aL > aH)
        /////////////////////////////
        val nonzero_indices = ArrayBuffer[Int]()
        for (ii <- 0 until (1 << n)) {
            var i = ii
            var t = 0
            for (_ <- 0 until n) {
                t <<= 1
                t += i & 1
                i >>= 1
            }
            var a = t & 1
            a <<= 1
            t >>= 1
            for (_ <- 2 until n+1) {
                a += t & 1
                a <<= 2
                t >>= 1
            }
            a += 1
            if (n <= 2) {
                a >>= 1
                a += 1
            }
            nonzero_indices += a
        }
        var s = 0
        for (i <- 0 until n) {
            s <<= 1
            s += i % 2
        }
        var pre = arrayN.const(complex(0, 0, 0, 0, 0))
        for ((num, i) <- nonzero_indices.zipWithIndex) {
            if (i == s) {
                // println('*', num.toBinaryString.reverse.padTo(N, '0').reverse.map{ case '1' => True case _ => False }.toList)
                pre = arrayN.store(List(pre) ++ num.toBinaryString.reverse.padTo(N, '0').reverse.map{ case '1' => True case _ => False }.toList ++ List(complex(aH, 0, 0, 0, 0)) : _*)
            } else {
                // println(i, num.toBinaryString.reverse.padTo(N, '0').reverse.map{ case '1' => True case _ => False }.toList)
                pre = arrayN.store(List(pre) ++ num.toBinaryString.reverse.padTo(N, '0').reverse.map{ case '1' => True case _ => False }.toList ++ List(complex(aL, 0, 0, 0, 0)) : _*)
            }
        }
        !! (states.head === pre)
        /////////////////////////////
        assert((countH & 1) == 0)
        // !! (/*(aH >= 0 & (*/bH > aH * (1 << (countH / 2)) | bH < -aH * (1 << (countH / 2)))//) |
        //     // (aH <= 0 & (bH > -aH * (1 << (countH / 2)) | bH < aH * (1 << (countH / 2)))))
        // !! (/*(aL >= 0 & (*/bL < aL * (1 << (countH / 2)) & bL > -aL * (1 << (countH / 2)))//) |
        //     // (aL <= 0 & (bL < -aL * (1 << (countH / 2)) & bL > aL * (1 << (countH / 2)))))
        !! (!(bH > aH * (1 << (countH / 2)) | bH < -aH * (1 << (countH / 2))) & (bL < aL * (1 << (countH / 2)) & bL > -aL * (1 << (countH / 2))))
        /////////////////////////////
        var post = arrayN.const(complex(0, 0, 0, 0, countH))
        for ((num, i) <- nonzero_indices.zipWithIndex) {
            if (i == s) {
                // println('*', num.toBinaryString.reverse.padTo(N, '0').reverse.map{ case '1' => True case _ => False }.toList)
                post = arrayN.store(List(post) ++ num.toBinaryString.reverse.padTo(N, '0').reverse.map{ case '1' => True case _ => False }.toList ++ List(complex(bH, 0, 0, 0, countH)) : _*)
            } else {
                // println(i, num.toBinaryString.reverse.padTo(N, '0').reverse.map{ case '1' => True case _ => False }.toList)
                post = arrayN.store(List(post) ++ num.toBinaryString.reverse.padTo(N, '0').reverse.map{ case '1' => True case _ => False }.toList ++ List(complex(bL, 0, 0, 0, countH)) : _*)
            }
        }
        !! (states.last === post)
        println(???) // valid
        // println(countGate)
        // println(evalToTerm(states.last))
    }
  }
}

object OEGroverBug {
    def main(args: Array[String]): Unit = {
        val gateCalls = QASMParser.extractGateCallsFromFile(args(0))
        new OEGroverBugClass(gateCalls._1, gateCalls._2).main(args)
    }
}
