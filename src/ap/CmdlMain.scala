/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap;

import ap.proof.ConstraintSimplifier
import ap.proof.tree.{ProofTree, QuantifiedTree}
import ap.proof.certificates.{Certificate, DotLineariser}
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.Quantifier
import ap.parameters.{GlobalSettings, Param}
import ap.parser.{SMTLineariser, IExpression, IBinJunctor, IInterpolantSpec,
                  INamedPart, PartName}
import ap.util.{Debug, Seqs, Timeout}

object CmdlMain {

  def printGreeting = {
    println("________       _____")                                 
    println("___  __ \\_________(_)________________________________")
    println("__  /_/ /_  ___/_  /__  __ \\  ___/  _ \\_  ___/_  ___/")
    println("_  ____/_  /   _  / _  / / / /__ /  __/(__  )_(__  )")
    println("/_/     /_/    /_/  /_/ /_/\\___/ \\___//____/ /____/")  
    println
    println("A Theorem Prover for First-Order Logic modulo Linear Integer Arithmetic")
    println("(CASC version 2012-04-18)")
    println
    println("(c) Philipp Rümmer, 2009-2012")
    println("(contributions by Angelo Brillout, Peter Baumgartner)")
    println("Free software under GNU General Public License (GPL).")
    println("Bug reports to ph_r@gmx.net")
    println
    println("For more information, visit http://www.philipp.ruemmer.org/princess.shtml")
  }
  
  def printUsage = {
    println("Usage: princess <option>* <inputfile>*")
    println
    printOptions
  }
  
  def printOptions = {
    println("Options:")
    println("  [+-]logo                      Print logo and elapsed time              (default: +)")
    println("  [+-]printTree                 Output the constructed proof tree        (default: -)")
    println("  -inputFormat=val              Specify format of problem file:          (default: auto)")
    println("                                  auto, pri, smtlib, tptp")
    println("  -printSMT=filename            Output the problem in SMT-Lib format     (default: \"\")")
    println("  -printDOT=filename            Output the proof in GraphViz format      (default: \"\")")
    println("  [+-]assert                    Enable runtime assertions                (default: -)")
    println("  -timeout=val                  Set a timeout in milliseconds            (default: infty)")
    println("  [+-]multiStrategy             Use a portfolio of different strategies  (default: -)")
    println("  -simplifyConstraints=val      How to simplify constraints:")
    println("                                  none:   not at all")
    println("                                  fair:   by fair construction of a proof (default)")
    println("                                  lemmas: by depth-first proof construction using lemmas")
    println("  [+-]traceConstraintSimplifier Show the constraint simplifications done (default: -)")
    println("  [+-]mostGeneralConstraint     Derive the most general constraint for this problem")
    println("                                (quantifier elimination for PA formulae) (default: -)")
    println("  [+-]dnfConstraints            Turn ground constraints into DNF         (default: +)")
    println("  -clausifier=val               Choose the clausifier (none, simple)     (default: none)")
    println("  [+-]posUnitResolution         Resolution of clauses with literals in   (default: +)")
    println("                                the antecedent")
    println("  -generateTriggers=val         Automatically generate triggers for quantified formulae")
    println("                                  none:  not at all")
    println("                                  total: for all total functions         (default)")
    println("                                  all:   for all functions")
    println("  -functionGC=val               Garbage-collect function terms")
    println("                                  none:  not at all")
    println("                                  total: for all total functions         (default)")
    println("                                  all:   for all functions")
    println("  [+-]tightFunctionScopes       Keep function application defs. local    (default: +)")
    println("  [+-]boolFunsAsPreds           Encode boolean functions as predicates?  (default: -)")
    println("                                (only used for SMT-LIB and TPTP)")
    println("  [+-]genTotalityAxioms         Generate totality axioms for functions   (default: +)")
    println("  -constructProofs=val          Extract proofs")
    println("                                  never")
    println("                                  ifInterpolating: if \\interpolant is present (default)")
    println("                                  always")
    println("  [+-]simplifyProofs            Simplify extracted proofs                (default: +)")
    println("  [+-]elimInterpolantQuants     Eliminate quantifiers from interpolants  (default: +)")
  }
  
  private def printSMT(prover : AbstractFileProver,
                       filename : String, settings : GlobalSettings) =
    if (Param.PRINT_SMT_FILE(settings) != "") {
      println
      
      def linearise : Unit = {
        import IExpression._
        val formulas = prover.interpolantSpecs match {
          case List() =>
            for (f <- prover.inputFormulas) yield removePartName(f)
          case IInterpolantSpec(left, right) :: _ => {
            def formula(name : PartName) =
              removePartName(prover.inputFormulas.find({
                               case INamedPart(`name`, _) => true
                               case _ => false
                             }).getOrElse(false))
              
            val common = formula(PartName.NO_NAME)
            
            // extract the order of formula parts from the first
            // interpolant specification; this does not quite do the right
            // thing for the axioms of uninterpreted functions, but should
            // work otherwise
            for (part <- left ++ right) yield (common ||| formula(part))
          }
        }

        SMTLineariser(formulas, prover.signature, filename)
      }
      
      if (Param.PRINT_SMT_FILE(settings) != "-") {
        println("Saving in SMT format to " +
                Param.PRINT_SMT_FILE(settings) + " ...")
        val out = new java.io.FileOutputStream(Param.PRINT_SMT_FILE(settings))
        Console.withOut(out) { linearise }
        out.close
      } else {
        linearise
      }
    }
  
  private def printDOTCertificate(cert : Certificate, settings : GlobalSettings) =
    if (Param.PRINT_DOT_CERTIFICATE_FILE(settings) != "") {
      println
      
      if (Param.PRINT_DOT_CERTIFICATE_FILE(settings) != "-") {
        println("Saving certificate in GraphViz format to " +
                Param.PRINT_DOT_CERTIFICATE_FILE(settings) + " ...")
        val out =
          new java.io.FileOutputStream(Param.PRINT_DOT_CERTIFICATE_FILE(settings))
        Console.withOut(out) { DotLineariser(cert) }
        out.close
      } else {
        DotLineariser(cert)
      }
    }
  
  private def determineInputFormat(filename : String,
                                   settings : GlobalSettings)
                                  : Param.InputFormat.Value =
    Param.INPUT_FORMAT(settings) match {
      case Param.InputFormat.Auto =>
        // try to guess the file type from the extension
        if (filename endsWith ".pri")
          Param.InputFormat.Princess
        else if (filename endsWith ".smt2")
          Param.InputFormat.SMTLIB
        else if (filename endsWith ".p")
          Param.InputFormat.TPTP
        else
          throw new Exception ("could not figure out the input format (recognised types: .pri, .smt2, .p)")
      case f => f
  }
  
  private def existentialConstantNum(p : ProofTree) : Int = p match {
    case QuantifiedTree(Quantifier.EX, consts, subtree) =>
      existentialConstantNum(subtree) + consts.size
    case t =>
      (for (st <- t.subtrees.iterator) yield existentialConstantNum(st)).sum
  }

  private var lastFilename : String = ""
  var positiveResult : String = "Theorem"
  var negativeResult : String = "CounterSatisfiable"
    
  var domain_size : ConstantTerm = new ConstantTerm("domain_size")

  def proveProblems(settings : GlobalSettings,
                    problems : Seq[(String, () => java.io.Reader)],
                    userDefStoppingCond : => Boolean) : Unit = {
    if (problems.isEmpty) {
      Console.withOut(Console.err) {
        println("No inputs given, exiting")
      }
      return
    }
    
    Debug.enableAllAssertions(Param.ASSERTIONS(settings))

    try {
          for ((filename, reader) <- problems) try {
            val timeBefore = System.currentTimeMillis
            
            Console.withOut(Console.err) {
              println("Loading " + filename + " ...")
            }
            lastFilename = (filename split "/").last stripSuffix ".p"
            val prover = if (Param.MULTI_STRATEGY(settings)) {
              val baseSettings = Param.INPUT_FORMAT.set(settings,
                                      determineInputFormat(filename, settings))
                                      
              /*
              val s1 = {
                var s = baseSettings
                s = Param.GENERATE_TOTALITY_AXIOMS.set(s, true)
                s = Param.TRIGGER_STRATEGY.set(s, Param.TriggerStrategyOptions.Maximal)
                s = Param.REVERSE_FUNCTIONALITY_PROPAGATION.set(s, true)
                s = Param.TIGHT_FUNCTION_SCOPES.set(s, false)
                s
              }
              val s2 = {
                var s = baseSettings
                s = Param.GENERATE_TOTALITY_AXIOMS.set(s, false)
                s = Param.TRIGGER_STRATEGY.set(s, Param.TriggerStrategyOptions.Maximal)
                s = Param.REVERSE_FUNCTIONALITY_PROPAGATION.set(s, false)
                s = Param.TIGHT_FUNCTION_SCOPES.set(s, false)
                s
              }
              val s3 = {
                var s = baseSettings
                s = Param.GENERATE_TOTALITY_AXIOMS.set(s, true)
                s = Param.TRIGGER_STRATEGY.set(s, Param.TriggerStrategyOptions.AllMaximal)
                s = Param.REVERSE_FUNCTIONALITY_PROPAGATION.set(s, true)
                s = Param.TIGHT_FUNCTION_SCOPES.set(s, true)
                s
              }
              
              val strategies =
                List((s1, true, "+reverseFunctionalityPropagation -tightFunctionScopes"),
                     (s2, false, "-genTotalityAxioms -tightFunctionScopes"),
                     (s3, true, "-triggerStrategy=allMaximal +reverseFunctionalityPropagation"))
              */
                                      
              val S = {
                var s = baseSettings
                s = Param.GENERATE_TOTALITY_AXIOMS.set(s, false)
                s = Param.TRIGGER_STRATEGY.set(s, Param.TriggerStrategyOptions.Maximal)
                s = Param.REVERSE_FUNCTIONALITY_PROPAGATION.set(s, false)
                s = Param.TIGHT_FUNCTION_SCOPES.set(s, false)
                s
              }
              val J = {
                var s = baseSettings
                s = Param.GENERATE_TOTALITY_AXIOMS.set(s, true)
                s = Param.TRIGGER_STRATEGY.set(s, Param.TriggerStrategyOptions.AllMaximal)
                s = Param.REVERSE_FUNCTIONALITY_PROPAGATION.set(s, true)
                s = Param.TIGHT_FUNCTION_SCOPES.set(s, true)
                s
              }
              val P = {
                var s = baseSettings
                s = Param.GENERATE_TOTALITY_AXIOMS.set(s, true)
                s = Param.TRIGGER_STRATEGY.set(s, Param.TriggerStrategyOptions.AllMaximal)
                s = Param.REVERSE_FUNCTIONALITY_PROPAGATION.set(s, false)
                s = Param.TIGHT_FUNCTION_SCOPES.set(s, false)
                s
              }
              val Y = {
                var s = baseSettings
                s = Param.GENERATE_TOTALITY_AXIOMS.set(s, false)
                s = Param.TRIGGER_STRATEGY.set(s, Param.TriggerStrategyOptions.Maximal)
                s = Param.REVERSE_FUNCTIONALITY_PROPAGATION.set(s, true)
                s = Param.TIGHT_FUNCTION_SCOPES.set(s, false)
                s
              }
              val W = {
                var s = baseSettings
                s = Param.GENERATE_TOTALITY_AXIOMS.set(s, false)
                s = Param.TRIGGER_STRATEGY.set(s, Param.TriggerStrategyOptions.Maximal)
                s = Param.REVERSE_FUNCTIONALITY_PROPAGATION.set(s, false)
                s = Param.TIGHT_FUNCTION_SCOPES.set(s, false)
                s = Param.TRIGGERS_IN_CONJECTURE.set(s, false)
                s
              }
              
              val strategies =
                List((S, false, "-genTotalityAxioms -tightFunctionScopes"),
                     (J, true, "-triggerStrategy=allMaximal +reverseFunctionalityPropagation"),
                     (P, true, "-triggerStrategy=allMaximal -tightFunctionScopes"),
                     (Y, false, "-genTotalityAxioms +reverseFunctionalityPropagation -tightFunctionScopes"),
                     (W, false, "-genTotalityAxioms -tightFunctionScopes -triggersInConjecture"))

              new ParallelFileProver(reader,
                                     Param.TIMEOUT(settings),
                                     true,
                                     userDefStoppingCond,
                                     strategies)
            } else {
              new IntelliFileProver(reader(),
                                    Param.TIMEOUT(settings),
                                    true,
                                    userDefStoppingCond,
                                    Param.INPUT_FORMAT.set(settings,
                                      determineInputFormat(filename, settings)))
            }

            Console.withOut(Console.err) {
              println
            }
            
            prover.result match {
              case Prover.Proof(tree) => {
                Console.err.println("Formula is valid, resulting " +
                        (if (Param.MOST_GENERAL_CONSTRAINT(settings))
                           "most-general "
                         else
                           "") + "constraint:")
                Console.err.println("" + tree.closingConstraint)
//                Console.err.println("Number of existential constants: " +
//                                    existentialConstantNum(tree))
                if (Param.PRINT_TREE(settings)) {
                  println
                  println("Proof tree:")
                  println(tree)
                }
                
                println("% SZS status " + positiveResult + " for " + lastFilename)
              }
              case Prover.ProofWithModel(tree, model) => {
                Console.err.println("Formula is valid, resulting " +
                        (if (Param.MOST_GENERAL_CONSTRAINT(settings))
                           "most-general "
                         else
                           "") + "constraint:")
                Console.err.println("" + tree.closingConstraint)
//                Console.err.println("Number of existential constants: " +
//                                    existentialConstantNum(tree))
                if (!model.isTrue) {
                  println
                  println("Concrete witness:")
                  println("" + model)
                }
                if (Param.PRINT_TREE(settings)) {
                  println
                  println("Proof tree:")
                  println(tree)
                }
                
                println("% SZS status " + positiveResult + " for " + lastFilename)
              }
              case Prover.NoProof(tree) =>  {
                Console.err.println("No proof found")
//                Console.err.println("Number of existential constants: " +
//                                    existentialConstantNum(tree))
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("false")
                }
                
                println("% SZS status GaveUp for " + lastFilename)
              }
              case Prover.CounterModel(model) =>  {
                Console.err.println("Formula is invalid, found a countermodel:")
                Console.err.println("" + model)
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("false")
                }
                
                println("% SZS status " + negativeResult + " for " + lastFilename)
              }
              case Prover.NoCounterModel =>  {
                Console.err.println("No countermodel exists, formula is valid")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("true")
                }
                
                println("% SZS status " + positiveResult + " for " + lastFilename)
              }
              case Prover.NoCounterModelCert(cert) =>  {
                Console.err.println("No countermodel exists, formula is valid")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("true")
                }
                Console.err.println
                Console.err.println("Certificate: " + cert)
                Console.err.println("Assumed formulae: " + cert.assumedFormulas)
                Console.err.println("Constraint: " + cert.closingConstraint)
                
                printDOTCertificate(cert, settings)

                println("% SZS status " + positiveResult + " for " + lastFilename)
              }
              case Prover.NoCounterModelCertInter(cert, inters) => {
                Console.err.println("No countermodel exists, formula is valid")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("true")
                }
//                println
//                println("Certificate: " + cert)
//                println("Assumed formulae: " + cert.assumedFormulas)
//                println("Constraint: " + cert.closingConstraint)
                Console.err.println
                Console.err.println("Interpolants:")
                for (i <- inters) Console.err.println(i)

                printDOTCertificate(cert, settings)
                
                println("% SZS status " + positiveResult + " for " + lastFilename)
              }
              case Prover.Model(model) =>  {
                Console.err.println("Formula is valid, satisfying assignment for the existential constants is:")
                Console.err.println("" + model)
                println("% SZS status " + positiveResult + " for " + lastFilename)
              }
              case Prover.NoModel =>  {
                Console.err.println("No satisfying assignment for the existential constants exists, formula is invalid")
                println("% SZS status " + negativeResult + " for " + lastFilename)
              }
              case Prover.TimeoutProof(tree) =>  {
                Console.err.println("Cancelled or timeout")
//                Console.err.println("Number of existential constants: " +
//                                    existentialConstantNum(tree))
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Current constraint:")
                  Timeout.withTimeoutMillis(1000) {
                    println("" + tree.closingConstraint)
                  }{
                    println("(timeout)")
                  }
                }
                if (Param.PRINT_TREE(settings)) {
                  println
                  println("Proof tree:")
                  println(tree)
                }
                println("% SZS status Timeout for " + lastFilename)
              }
              case Prover.TimeoutModel | Prover.TimeoutCounterModel =>  {
                Console.err.println("Cancelled or timeout")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Current constraint:")
                  println("false")
                }
                println("% SZS status Timeout for " + lastFilename)
              }
            }
            
            val timeAfter = System.currentTimeMillis
            
            Console.withOut(Console.err) {
              println
              if (Param.LOGO(settings))
                println("" + (timeAfter - timeBefore) + "ms")
            }
            
            prover match {
              case prover : AbstractFileProver => printSMT(prover, filename, settings)
              case _ => // nothing
            }
            
            /* println
            println(ap.util.Timer)
            ap.util.Timer.reset */
          } catch {
            case _ : StackOverflowError => Console.withOut(Console.err) {
              println("Stack overflow, giving up")
              // let's hope that everything is still in a valid state
            }
            case _ : OutOfMemoryError => Console.withOut(Console.err) {
              println("Out of memory, giving up")
              System.gc
              // let's hope that everything is still in a valid state
            }
          }
    } catch {
      case e : Throwable => {
        Console.withOut(Console.err) {
          println("ERROR: " + e.getMessage)
//         e.printStackTrace
        }
        println("% SZS status Error for " + lastFilename)
        return
      }
    }
  }

  def main(args: Array[String]) : Unit = {
    val (settings, inputs) =
      try { // switch on proof construction by default in the iPrincess version
            GlobalSettings.fromArguments(args, GlobalSettings.DEFAULT)
          } catch {
      case e : Throwable => {
        Console.withOut(Console.err) {
          printGreeting
          println
          println(e.getMessage)
          println
          printUsage
        }
        return
      }
    }

    if (Param.LOGO(settings)) Console.withOut(Console.err) {
      printGreeting
      println
    }
    
    proveProblems(settings,
                  for (name <- inputs.view)
                  yield (name,
                         () => new java.io.BufferedReader (
                               new java.io.FileReader(new java.io.File (name)))),
                  false)
  }
}
