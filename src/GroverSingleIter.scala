import ap.Quantum
import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT.BoolADT.{True, False}
import scala.collection.mutable.ListBuffer
import IExpression._
import SimpleAPI.ProverStatus

class GroverSingleIterClass(val n: Int) extends Quantum(n) {
  SimpleAPI.withProver(enableAssert = debug) { p => import p._

    val states = ListBuffer(createConstant(arrayN.sort))
    val index = createConstants(Q, Sort.Bool)

    val al = createConstant(Sort.Integer)
    val ah = createConstant(Sort.Integer)
    val aL = createConstant(Sort.Integer)
    val aH = createConstant(Sort.Integer)

    // This is one iteration of Grover's algorithm
    // with the hidden item determined by $index.
    scope {
        for (i <- 0 until Q) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! ((index(i) === False & X(i, before, after)) | (index(i) === True & before === after))
        }
        //
        {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! (CqZ(Q, before, after))
        }
        //
        for (i <- 0 until Q) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! ((index(i) === False & X(i, before, after)) | (index(i) === True & before === after))
        }
        for (i <- 0 until Q) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! (H(i, before, after))
        }
        for (i <- 0 until Q) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! (X(i, before, after))
        }
        //
        {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! (CqZ(Q, before, after))
        }
        //
        for (i <- 0 until Q) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! (X(i, before, after))
        }
        for (i <- 0 until Q) {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! (H(i, before, after))
        }
        {
            val before = states.last
            states += createConstant(arrayN.sort)
            val after = states.last
            !! (after === vec_negate(before))
        }

        !! (states.head  === arrayN.store(List(arrayN.const(complex(al, 0, 0, 0, 0)))
                                        ++ index ++ List(complex(ah, 0, 0, 0, 0)) : _*))
        !! (states.last  === arrayN.store(List(arrayN.const(complex(aL, 0, 0, 0, 2*Q)))
                                        ++ index ++ List(complex(aH, 0, 0, 0, 2*Q)) : _*))
        
        !! (al + ah > 0)
        !! (al * ((1 << Q) - 1) > ah)

        !! (! ((aL < al * (1 << Q)) & (aH > ah * (1 << Q))))

        for (i <- 0 until Q) {
            if (i % 2 == 1)
                !! (index(i) === True)
            else
                !! (index(i) === False)
        }

        val proverResult = ???
        // println(countGate)
        println(proverResult) // UNsat
        if (proverResult == ProverStatus.Sat) {
        }
    }
  }
}

object GroverSingleIter {
    def main(args: Array[String]): Unit = {
        new GroverSingleIterClass(args(0).toInt).main(args)
    }
}