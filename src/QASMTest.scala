
import ap.SimpleAPI
import ap.parser._
import ap.basetypes.IdealInt
import ap.theories.ADT
import ADT.BoolADT.{True, False}
import ap.theories.arrays._
import scala.collection.mutable.ListBuffer

class QuantumCircuit (val N: Int, val LGQ: List[(String, List[Int])]) extends App {

  val debug = false // change to false for much faster solving

  ap.util.Debug.enableAllAssertions(debug)

  import IExpression._

  val (complexSort, complex, Seq(a, b, c, d, k)) =
    ADT.createRecordType("Complex", List(("a", Sort.Integer),
                                         ("b", Sort.Integer),
                                         ("c", Sort.Integer),
                                         ("d", Sort.Integer),
                                         ("k", Sort.Nat)))

  // This just assumes (and does not verify) that the k's are consistent
  def complexPlus(s : ITerm, t : ITerm) : ITerm =
    complex(a(s) + a(t), b(s) + b(t), c(s) + c(t), d(s) + d(t), k(s))

  // This just assumes (and does not verify) that the k's are consistent
  def complexMinus(s : ITerm, t : ITerm) : ITerm =
    complex(a(s) - a(t), b(s) - b(t), c(s) - c(t), d(s) - d(t), k(s))

  def omegaMult(s : ITerm) : ITerm =
    complex(-d(s), a(s), b(s), c(s), k(s))

  def intMult(s : ITerm, n : IdealInt) : ITerm =
    complex(a(s) * n, b(s) * n, c(s) * n, d(s) * n, k(s))

  def sqrt2Div(s : ITerm) : ITerm =
    complex(a(s), b(s), c(s), d(s), k(s) + 1)

  def kInc2(s : ITerm) : ITerm =
    complex(a(s) * 2, b(s) * 2, c(s) * 2, d(s) * 2, k(s) + 2)

  def setK1(s : ITerm) : ITerm =
    complex(a(s), b(s), c(s), d(s), 1)

  val vectorOps = Vector(
    CombArray.CombinatorSpec("vec_plus", List(0, 0), 0,
                             v(2, complexSort) === complexPlus(v(0, complexSort), v(1, complexSort))),
    CombArray.CombinatorSpec("vec_minus", List(0, 0), 0,
                             v(2, complexSort) === complexMinus(v(0, complexSort), v(1, complexSort))),
    CombArray.CombinatorSpec("vec_omegaMult", List(0), 0,
                             v(1, complexSort) === omegaMult(v(0, complexSort))),
    CombArray.CombinatorSpec("vec_negate", List(0), 0,
                             v(1, complexSort) === intMult(v(0, complexSort), -1)),
    CombArray.CombinatorSpec("vec_sqrt2Div", List(0), 0,
                             v(1, complexSort) === sqrt2Div(v(0, complexSort))),
    CombArray.CombinatorSpec("vec_setK1", List(0), 0,
                             v(1, complexSort) === setK1(v(0, complexSort)))
  )

  def bools(n : Int) = for (_ <- 0 until n) yield Sort.Bool
  def nFalse(n : Int) = (for (_ <- 0 until n) yield False).toList
  def nTrue(n : Int) = (for (_ <- 0 until n) yield True).toList

  val CartTheory =
    new CartArray(bools(N), complexSort, 3, vectorOps)
  
  val arrayN  = CartTheory.extTheories(bools(N))
  val arrayN1 = CartTheory.extTheories(bools(N - 1))

  import CartTheory.{proj, sel, sto}

  val Seq(vec_plus, vec_minus,
          vec_omegaMult, vec_negate,
          vec_sqrt2Div, vec_setK1) = CartTheory.combinators

  def selectN(ar : ITerm, indexes : ITerm*) : ITerm =
    IFunApp(arrayN.select, List(ar) ++ indexes)

  def X(k : Int, s : ITerm, Xs : ITerm) : IFormula =
    proj(Xs, k -> False) === proj(s, k -> True) &
    proj(Xs, k -> True) === proj(s, k -> False)

  def Y(k : Int, s : ITerm, Ys : ITerm) : IFormula =
    proj(Ys, k -> False) === vec_negate(vec_omegaMult(vec_omegaMult(proj(s, k -> True)))) &
    proj(Ys, k -> True) === vec_omegaMult(vec_omegaMult(proj(s, k -> False)))

  def Z(k : Int, s : ITerm, Zs : ITerm) : IFormula =
    proj(Zs, k -> False) === proj(s, k -> False) &
    proj(Zs, k -> True) === vec_negate(proj(s, k -> True))

  def H(k : Int, s : ITerm, hs : ITerm) : IFormula =
    proj(hs, k -> False) ===
      vec_sqrt2Div(vec_plus(proj(s, k -> False), proj(s, k -> True))) &
    proj(hs, k -> True) ===
      vec_sqrt2Div(vec_minus(proj(s, k -> False), proj(s, k -> True)))

  def S(k : Int, s : ITerm, Ss : ITerm) : IFormula =
    proj(Ss, k -> False) === proj(s, k -> False) &
    proj(Ss, k -> True) === vec_omegaMult(vec_omegaMult(proj(s, k -> True)))

  def T(k : Int, s : ITerm, Ts : ITerm) : IFormula =
    proj(Ts, k -> False) === proj(s, k -> False) &
    proj(Ts, k -> True) === vec_omegaMult(proj(s, k -> True))

  def CX(c : Int, t : Int, s : ITerm, cxs : ITerm) : IFormula =
    proj(cxs, c -> False)            === proj(s, c -> False) &
    proj(cxs, c -> True, t -> False) === proj(s, c -> True, t -> True) &
    proj(cxs, c -> True, t -> True)  === proj(s, c -> True, t -> False)

  def CZ(c : Int, t : Int, s : ITerm, CZs : ITerm) : IFormula =
    proj(CZs, c -> False)            === proj(s, c -> False) &
    proj(CZs, c -> True, t -> False) === proj(s, c -> True, t -> False) &
    proj(CZs, c -> True, t -> True)  === vec_negate(proj(s, c -> True, t -> True))

  def CCX(c : Int, d : Int, t : Int, s : ITerm, CCXs : ITerm) : IFormula =
    proj(CCXs, c -> False)            === proj(s, c -> False) &
    proj(CCXs, d -> False)            === proj(s, d -> False) &
    proj(CCXs, c -> True, d -> True, t -> False) === proj(s, c -> True, d -> True, t -> True) &
    proj(CCXs, c -> True, d -> True, t -> True)  === proj(s, c -> True, d -> True, t -> False)

  SimpleAPI.withProver(enableAssert = debug) { p =>
    import p._

    addTheory(CartTheory)

    val states = ListBuffer(createConstant("s0", arrayN.sort))

    scope {
        for (GQ <- LGQ) {
            val before = states.last
            states += createConstant("s" + (states.size), arrayN.sort)
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
      !! (states.head  === sto(arrayN.const(complex(0, 0, 0, 0, 0)),
                               nFalse(N) ++ List(complex(1, 0, 0, 0, 0)) : _*))

      println(???) // sat
    //   println(evalToTerm(states.last))
    }
  }

}

import scala.io.Source
import scala.util.parsing.combinator.RegexParsers

object QASMParser extends RegexParsers {
  // Define the gate name pattern
  private val gateName = """[a-zA-Z]+""".r

  // Define the qubit index pattern
  private val qubitIndex = """qubits\[\d+\]""".r

  // Define the gate parser
  private val gate: Parser[(String, List[Int])] =
    gateName ~ rep1sep(qubitIndex, ",") <~ ";" ^^ {
      case name ~ qubits => (name, qubits.map(s => s.substring(7, s.length - 1).toInt))
    }

  // Define the qubit number parser
  private val qubit: Parser[Int] =
    "qreg qubits[" ~> """\d+""".r <~ "];" ^^ (_.toInt)

  private val ignoredLine: Parser[Unit] = """OPENQASM 2.0;\ninclude \"qelib1.inc\";""".r ^^^ ()

  // Define the program parser
  private val program: Parser[(Int, List[(String, List[Int])])] =
    ignoredLine ~> qubit ~ rep(gate) map { case q ~ gates => (q, gates) }

  // Define a method to parse a QASM file and extract the gate calls and their applied qubits
  def extractGateCallsFromFile(filePath: String): (Int, List[(String, List[Int])]) = {
    val qasm = Source.fromFile(filePath).mkString
    parseAll(program, qasm) match {
      case Success(result, _) => result
      case failure: NoSuccess => throw new RuntimeException(s"Failed to parse QASM: ${failure.msg}")
    }
  }
}

object QASMTest {
    def main(args: Array[String]): Unit = {
        val gateCalls = QASMParser.extractGateCallsFromFile(args(0))
        // println(gateCalls._1)
        // println(gateCalls._2)
        new QuantumCircuit(gateCalls._1, gateCalls._2).main(args)
    }
}