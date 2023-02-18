
import ap.Quantum
import ap.SimpleAPI
import ap.parser._
import IExpression._
import scala.collection.mutable.ListBuffer

class QuantumCircuit (val N: Int, val LGQ: List[(String, List[Int])]) extends Quantum(N) {
    SimpleAPI.withProver(enableAssert = debug) { p => import p._

    val states = ListBuffer(createConstant(arrayN.sort))

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
        !! (states.head  === arrayN.store(List(arrayN.const(complex(0, 0, 0, 0, 0))) ++
                                          nFalse(N) ++ List(complex(1, 0, 0, 0, 0)) : _*))

        println(???) // sat
        // println(evalToTerm(states.last))
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

  // Define the program parser
  private val program: Parser[(Int, List[(String, List[Int])])] =
    """OPENQASM 2.0;\ninclude \"qelib1.inc\";""".r ~> qubit ~ rep(gate) map { case q ~ gates => (q, gates) }

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