/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2014 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package ap.util;

object Combinatorics {

  def genSubsequences[A](seq : Seq[A], num : Int) : Iterator[List[A]] =
    if (num == 0)
      Iterator single List()
    else
      for (i <- (0 until (seq.size - num + 1)).iterator;
           p = seq(i);
           s <- genSubsequences(seq.view(i + 1, seq.size), num - 1))
      yield p :: s

  def genSubsequencesWithDups[A](seq : Seq[A], num : Int) : Iterator[List[A]] =
    if (num == 0)
      Iterator single List()
    else
      for (i <- (0 until seq.size).iterator;
           p = seq(i);
           s <- genSubsequencesWithDups(seq.view(i, seq.size), num - 1))
      yield p :: s

  def cartesianProduct[A](seqs : List[Seq[A]]) : Iterator[List[A]] = seqs match {
    case List() =>
      Iterator single List()
    case s :: otherSeqs =>
      for (rem <- cartesianProduct(otherSeqs); a <- s.iterator) yield a :: rem
  }

  def genSubsequences[A](seqs : Seq[Seq[A]],
                         nums : Seq[Int]) : Iterator[List[A]] = {
    val subSeqs =
      (for ((seq, num) <- seqs.iterator zip nums.iterator)
       yield genSubsequences(seq, num).toSeq).toList
    for (comb <- cartesianProduct(subSeqs)) yield comb.flatten
  }

  def genSubsequencesWithDups[A](seqs : Seq[Seq[A]],
                                 nums : Seq[Int]) : Iterator[List[A]] = {
    val subSeqs =
      (for ((seq, num) <- seqs.iterator zip nums.iterator)
       yield genSubsequencesWithDups(seq, num).toSeq).toList
    for (comb <- cartesianProduct(subSeqs)) yield comb.flatten
  }

  def genCoveredVectors(nums : List[Int]) : Iterator[List[Int]] = nums match {
    case List() =>
      Iterator single List()
    case n :: otherNums =>
      for (vec <- genCoveredVectors(otherNums); i <- (0 to n).iterator)
      yield i :: vec
  }

  def genSubMultisets[A](seq : Seq[A]) : Iterator[List[A]] = {
    val uniqueEls = seq.distinct.toList
    val elNums = for (a <- uniqueEls) yield (seq count (_ == a))

    for (nums <- genCoveredVectors(elNums))
    yield (for ((num, el) <- nums.iterator zip uniqueEls.iterator;
                _ <- (0 until num).iterator) yield el).toList
  }

}
