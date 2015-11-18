/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2015 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
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

package ap.proof.goal;

import ap.basetypes.HeapCollector
import ap.terfor.ConstantTerm
import ap.terfor.preds.Predicate

object TaskInfoCollector {
  
  def EMPTY(abbrevLabels : Map[Predicate, Predicate]) : TaskInfoCollector =
    new TaskInfoCollector(Set.empty, false, abbrevLabels, Set(), Set())
  
}

class TaskInfoCollector private (val constants : Set[ConstantTerm],
                                 val containsLazyMatchTask : Boolean,
                                 abbrevLabels : Map[Predicate, Predicate],
                                 val occurringAbbrevs : Set[Predicate],
                                 val occurringAbbrevDefs : Set[Predicate])
      extends HeapCollector[Task, TaskInfoCollector] {

  def +(task : Task, otherInfos : TaskInfoCollector) : TaskInfoCollector = {
    val (taskConstants, newAbbrevs)
            : (Set[ConstantTerm], Set[Predicate]) = task match {
      case task : FormulaTask =>
        (task.formula.constants,
         if (abbrevLabels.isEmpty)
           Set.empty
         else
           task.formula.predicates & abbrevLabels.keySet)
      case _ =>
        (Set.empty, Set.empty)
    }

    val newDefs : Set[Predicate] = task match {
      case task : BetaFormulaTask if (!newAbbrevs.isEmpty) =>
        newAbbrevs filter {
          p => task.formula.predicates contains abbrevLabels(p)
        }
      case _ =>
        Set.empty
    }

    new TaskInfoCollector(this.constants ++
                            taskConstants ++
                            otherInfos.constants,
                          this.containsLazyMatchTask ||
                            task.isInstanceOf[LazyMatchTask] ||
                            otherInfos.containsLazyMatchTask,
                          this.abbrevLabels,
                          this.occurringAbbrevs ++
                            (newAbbrevs -- newDefs) ++
                            otherInfos.occurringAbbrevs,
                          this.occurringAbbrevDefs ++
                            newDefs ++
                            otherInfos.occurringAbbrevDefs)
  }
  
}
