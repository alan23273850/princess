import ap.Quantum
import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT.BoolADT.{True, False}
import IExpression._

object EPRTest extends Quantum(2) {
  SimpleAPI.withProver(enableAssert = debug) { p => import p._

    val x0 = createConstant("x0", arrayN.sort)
    val x = createConstant("x", arrayN.sort)
    val y = createConstant("y", arrayN.sort)
    val z = createConstant("z", arrayN.sort)
    val y1 = createConstant("y1", arrayN.sort)
    val z1 = createConstant("z1", arrayN.sort)

    val comp0 = createConstant("comp0", complexSort)
    val comp1 = createConstant("comp1", complexSort)
    val comp2 = createConstant("comp2", complexSort)
    val comp3 = createConstant("comp3", complexSort)

    // This is the EPR circuit example that
    // transforms |00> to half |00> and half |11>
    scope {
      !! (H(0, x, y))
      !! (CX(0, 1, y, z))
//    !! (H(0, y, z))
      !! (x0 === arrayN.const(complex(0, 0, 0, 0, 0)))
      !! (x  === arrayN.store(List(x0) ++ nFalse(2) ++ List(complex(1, 0, 0, 0, 0)) : _*))
//      !! (selectN(x, False :: nFalse(2 - 1) : _*) === complex(1, 0, 0, 0, 0))
  //    !! (selectN(x, True  :: nFalse(2 - 1) : _*) === complex(2, 2, 2, 2, 1))
      !! (selectN(z, False :: nFalse(2 - 1) : _*) === comp0)
      !! (selectN(z, False :: nTrue(2 - 1) : _*) === comp1)
      !! (selectN(z, True  :: nFalse(2 - 1) : _*) === comp2)
      !! (selectN(z, True  :: nTrue(2 - 1) : _*) === comp3)
      println(???) // sat
    //   println(evalToTerm(z))
      println(evalToTerm(x))
      println(evalToTerm(comp0))
      println(evalToTerm(comp1))
      println(evalToTerm(comp2))
      println(evalToTerm(comp3))
    }
/*
    scope {
      val qbits = createConstants(2, Sort.Bool)

      // Assert that all k-components are initially 1
      !! (x === vec_setK1N(x0))

      // Encoding of the circuit
      !! (H(1, x, y))
      !! (H(1, y, z))
      !! (H(2, z, y1))
      !! (H(2, y1, z1))

      // Assertion: x, z coincide modulo normalization
      ?? (kInc2(kInc2(selectN(x, qbits : _*))) === selectN(z1, qbits : _*))

      println(???) // valid
    }*/


  }

}
