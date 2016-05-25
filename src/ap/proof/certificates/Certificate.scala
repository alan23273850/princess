/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2016 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.proof.certificates

import ap.terfor.{TermOrder, SortedWithOrder, ConstantTerm}
import ap.terfor.conjunctions.Conjunction
import ap.util.{Debug, FilterIt, Seqs}

import scala.collection.mutable.ArrayBuffer

object Certificate {
  
  private val AC = Debug.AC_CERTIFICATES
  
}

/**
 * Datastructures used to express and extract whole, detailed proofs, which can
 * independently be checked and be used for further processing (e.g., to compute
 * interpolants). Certificates are trees/proof terms, with the following class
 * as the abstract superclass of all tree nodes. Proofs are more or less tableau
 * proofs, with rule applications assuming certain formulae on a branch and
 * producing new formulae.
 */
abstract class Certificate {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(Certificate.AC,
                   (closingConstraint isSortedBy order) &&
                   size == localProvidedFormulas.size &&
                   (assumedFormulas forall (order isSortingOf _)))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  /**
   * The constraint resulting from this proof
   */
  val closingConstraint : Conjunction
  
  /**
   * Formulae that the proof assumes to be present on this branch (i.e.,
   * premisses of rules applied in the proof). We assume that all formulae
   * live in the antecedent.
   */
  lazy val assumedFormulas : Set[CertFormula] =
    localAssumedFormulas ++
    (for ((cert, providedFormulas) <-
            iterator zip localProvidedFormulas.iterator;
          f <- FilterIt(cert.assumedFormulas.iterator,
                        (f : CertFormula) => !(providedFormulas contains f)))
     yield f)
  
  val localAssumedFormulas : Set[CertFormula]
  
  /**
   * Formulae that are introduced into the antecedent by this rule application
   * (one set for each subproof). This will implicitly simplify formulae (all
   * simplifications that are built into the datastructures are carried out).
   */
  val localProvidedFormulas : Seq[Set[CertFormula]]

  val order : TermOrder

  /**
   * Set of constants occurring in this certificate. By default this will
   * contain the set of all constants in sub-certificates, as well as
   * constants in assumed formulas.
   */
  lazy val constants : Set[ConstantTerm] =
    Seqs.union((for (cert <- subCertificates.iterator)
                yield cert.constants) ++
               (for (f <- localAssumedFormulas.iterator)
                yield f.constants)) -- localBoundConstants

  /**
   * Constants bound by the root operator of the certificate.
   */
  val localBoundConstants : Set[ConstantTerm] = Set()

  def inferenceCount : Int =
    (1 /: this.subCertificates) { case (num, cert) => num + cert.inferenceCount }

  def apply(i : Int) : Certificate
  def length : Int
  def iterator : Iterator [Certificate]
  
  def size = length

  def subCertificates = new IndexedSeq[Certificate] {
    def apply(i : Int) : Certificate = Certificate.this.apply(i)
    def length : Int = Certificate.this.length
    override def iterator = Certificate.this.iterator
  }
  
  def update(newSubCerts : Seq[Certificate]) : Certificate
}

////////////////////////////////////////////////////////////////////////////////

object PartialCertificate {
  
  private val AC = Debug.AC_CERTIFICATES
  
  val IDENTITY =
    new PartialCertificate((x : Seq[Certificate]) => x.head, List(None), null, 1)
  
  def apply(comb : Seq[Certificate] => Certificate, arity : Int) =
    new PartialCertificate(comb, Array.fill(arity)(None), null, arity)
  
  def apply(comb : Seq[Certificate] => Certificate,
            providedFormulas : Seq[Set[CertFormula]],
            alt : Certificate => Certificate,
            arity : Int) =
    new PartialCertificate(comb,
                           for (pf <- providedFormulas) yield Some(pf),
                           alt, arity)
  
}

/**
 * Class to store fragments of certificates. Such fragments can be seen as
 * functions from sequences of certificates (the certificates derived from
 * some subproofs) to certificates. In this sense, every rule application
 * is justified by a partial certificate.
 * 
 * The class also offers the possibility of proof pruning, applied when a 
 * sub-certificate does not actually use any of the formulae generated by a
 * rule application. In this case, instead of applying <code>comb</code> to all
 * sub-certificate, only <code>alt</code> is applied to a selected
 * sub-certificate
 */
class PartialCertificate private (comb : Seq[Certificate] => Certificate,
                                  providedFormulas
                                          : Seq[Option[Set[CertFormula]]],
                                  alt : Certificate => Certificate,
                                  val arity : Int)
      extends (Seq[Certificate] => Certificate) {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(PartialCertificate.AC, providedFormulas.size == arity)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def apply(subCerts : Seq[Certificate]) : Certificate = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(PartialCertificate.AC, arity == subCerts.size)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    comb(subCerts)
  }

  def compose(that : Seq[PartialCertificate]) : PartialCertificate = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(PartialCertificate.AC, arity == that.size)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    val newArity = (that.iterator map (_.arity)).sum
    
    val newComb = (certs : Seq[Certificate]) => {
      val subRes = new ArrayBuffer[Certificate]
      var offset : Int = 0
      for (pc <- that) {
        val newOffset = offset + pc.arity
        subRes += pc(certs.slice(offset, newOffset))
        offset = newOffset
      }
      apply(subRes)
    }
    
    PartialCertificate(newComb, newArity)
  }
  
  /**
   * Bind the first argument of the partial certificate, resulting in a
   * partial certificate with one fewer free arguments, or (in case proof
   * pruning can be performed) a complete certificate
   */
  def bindFirst(cert : Certificate)
               : Either[PartialCertificate, Certificate] = providedFormulas.head match {
    case Some(fors) if (Seqs.disjoint(cert.assumedFormulas, fors)) =>
      // Then the formulas generated by the rule application in the first
      // branch are not actually needed, and we just just take the
      // sub-certificate as certificate altogether
      Right(alt(cert))
    case _ if (arity == 1) =>
      Right(comb(List(cert))) 
    case _ =>
      Left(new PartialCertificate(certs => comb(List(cert) ++ certs),
                                  providedFormulas.tail,
                                  alt,
                                  arity - 1))
  }
}
