// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.label;

import java.util.Iterator;
import java.util.List;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AbstractAuxiliaryContractRule;
import de.uka.ilkd.key.rule.BlockContractExternalRule;
import de.uka.ilkd.key.rule.BlockContractInternalRule;
import de.uka.ilkd.key.rule.LoopContractExternalRule;
import de.uka.ilkd.key.rule.LoopContractInternalRule;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.WhileInvariantRule;

/**
 * This {@link TermLabelRefactoring} removes the supported {@link TermLabel}
 * in check branches. These are:
 * <ul>
 *    <li>{@link AbstractAuxiliaryContractRule}: Pre</li>
 *    <li>{@link UseOperationContractRule}: Pre</li>
 *    <li>{@link UseOperationContractRule}: Null reference</li>
 *    <li>{@link WhileInvariantRule}: Invariant Initially Valid</li>
 * </ul>
 * @author Martin Hentschel
 */
public class RemoveInCheckBranchesTermLabelRefactoring implements TermLabelRefactoring {
   /**
    * The {@link Name} of the supported {@link TermLabel}.
    */
   private final Name termLabelNameToRemove;

   /**
    * Constructor.
    * @param termLabelNameToRemove The {@link Name} of the supported {@link TermLabel}.
    */
   public RemoveInCheckBranchesTermLabelRefactoring(Name termLabelNameToRemove) {
      assert termLabelNameToRemove != null;
      this.termLabelNameToRemove = termLabelNameToRemove;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<Name> getSupportedRuleNames() {
      return ImmutableSLList.<Name>nil().prepend(UseOperationContractRule.INSTANCE.name())
                                        .prepend(WhileInvariantRule.INSTANCE.name())
                                        .prepend(BlockContractInternalRule.INSTANCE.name())
                                        .prepend(BlockContractExternalRule.INSTANCE.name())
                                        .prepend(LoopContractInternalRule.INSTANCE.name())
                                        .prepend(LoopContractExternalRule.INSTANCE.name());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public RefactoringScope defineRefactoringScope(TermLabelState state,
                                                  Services services,
                                                  PosInOccurrence applicationPosInOccurrence,
                                                  Term applicationTerm,
                                                  Rule rule,
                                                  Goal goal,
                                                  Object hint, 
                                                  Term tacletTerm) {
      if (goal != null) {
         if (rule instanceof UseOperationContractRule &&
               (goal.node().getNodeInfo().getBranchLabel().startsWith("Pre") ||
                goal.node().getNodeInfo().getBranchLabel().startsWith("Null reference"))) {
            return RefactoringScope.SEQUENT;
         }
         else if (rule instanceof WhileInvariantRule &&
                  goal.node().getNodeInfo().getBranchLabel().startsWith("Invariant Initially Valid")) {
            return RefactoringScope.SEQUENT;
         }
         else if (rule instanceof AbstractAuxiliaryContractRule &&
                  goal.node().getNodeInfo().getBranchLabel().startsWith("Precondition")) {
              return RefactoringScope.SEQUENT;
           }
         else {
            return RefactoringScope.NONE;
         }
      }
      else {
         return RefactoringScope.NONE;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void refactorLabels(TermLabelState state,
                               Services services,
                               PosInOccurrence applicationPosInOccurrence,
                               Term applicationTerm,
                               Rule rule,
                               Goal goal,
                               Object hint, 
                               Term tacletTerm,
                               Term term,
                               List<TermLabel> labels) {
      Iterator<TermLabel> iter = labels.iterator();
      while (iter.hasNext()) {
         TermLabel next = iter.next();
         if (termLabelNameToRemove.equals(next.name())) {
            iter.remove();
         }
      }
   }
}