// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.mergerule.predicateabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractionPredicate;
import de.uka.ilkd.key.gui.mergerule.MergeProcedureCompletion;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.merge.MergePartner;
import de.uka.ilkd.key.rule.merge.procedures.MergeWithPredicateAbstraction;
import de.uka.ilkd.key.rule.merge.procedures.MergeWithPredicateAbstractionFactory;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;
import de.uka.ilkd.key.util.mergerule.SymbolicExecutionState;

/**
 * Completion class for {@link MergeWithPredicateAbstraction}.
 *
 * @author Dominic Scheurer
 */
public class PredicateAbstractionCompletion extends
      MergeProcedureCompletion<MergeWithPredicateAbstraction> {

   /*
    * (non-Javadoc)
    * 
    * @see de.uka.ilkd.key.gui.joinrule.JoinProcedureCompletion#complete(de.uka.
    * ilkd.key.rule.join.JoinProcedure, de.uka.ilkd.key.proof.Goal)
    */
   @Override
   public MergeWithPredicateAbstraction complete(
         MergeWithPredicateAbstraction proc,
         Pair<Goal, PosInOccurrence> joinGoalPio,
         Collection<MergePartner> partners) {
      final Services services = joinGoalPio.first.proof().getServices();

      // Compute the program variables that are different in the
      // respective states.

      final SymbolicExecutionState joinState =
            MergeRuleUtils.sequentToSEPair(joinGoalPio.first.node(),
                  joinGoalPio.second, services);

      final ImmutableList<SymbolicExecutionState> partnerStates =
            MergeRuleUtils.sequentsToSEPairs(partners);

      final ArrayList<LocationVariable> differingLocVars =
            new ArrayList<LocationVariable>();

      MergeRuleUtils
            .getUpdateLeftSideLocations(joinState.first)
            .forEach(v -> {
               // The meaning of the following statement corresponds to
               // partnerStates.fold("right value for v differs", false)
                  final boolean isDifferent =
                        StreamSupport
                              .stream(partnerStates.spliterator(), false)
                              .collect(
                                    Collectors
                                          .reducing(
                                                false,
                                                partner -> !MergeRuleUtils
                                                      .getUpdateRightSideForSafe(
                                                            partner
                                                                  .getSymbolicState(),
                                                            v)
                                                      .equals(
                                                            MergeRuleUtils
                                                                  .getUpdateRightSideForSafe(
                                                                        joinState
                                                                              .getSymbolicState(),
                                                                        v)), (
                                                      b1, b2) -> (b1 || b2)));

                  if (isDifferent) {
                     differingLocVars.add(v);
                  }
               });

      final AbstractionPredicatesChoiceDialog dialog =
            new AbstractionPredicatesChoiceDialog(joinGoalPio.first,
                  differingLocVars);

      assert proc instanceof MergeWithPredicateAbstractionFactory : "Exptected an procedure of type JoinWithPredicateAbstractionFactory.";

      final MergeWithPredicateAbstractionFactory procF =
            (MergeWithPredicateAbstractionFactory) proc;

      dialog.setVisible(true);

      final AbstractionPredicatesChoiceDialog.Result userInput =
            dialog.getResult();

      final ArrayList<AbstractionPredicate> chosenPreds =
            userInput.getRegisteredPredicates();

      // A null-pointer in the chosen predicates means that
      // the user has pressed the cancel button.
      if (chosenPreds == null) {
         return proc;
      }
      else {
         return procF.instantiate(chosenPreds, userInput.getLatticeType(),
               userInput.getAbstractDomElemUserChoices());
      }
   }
}
