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

package de.uka.ilkd.key.gui.joinrule.predicateabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractionPredicate;
import de.uka.ilkd.key.gui.joinrule.JoinProcedureCompletion;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.join.procedures.JoinWithPredicateAbstraction;
import de.uka.ilkd.key.rule.join.procedures.JoinWithPredicateAbstractionFactory;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;
import de.uka.ilkd.key.util.joinrule.SymbolicExecutionState;

/**
 * Completion class for {@link JoinWithPredicateAbstraction}.
 *
 * @author Dominic Scheurer
 */
public class PredicateAbstractionCompletion extends
        JoinProcedureCompletion<JoinWithPredicateAbstraction> {

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.key.gui.joinrule.JoinProcedureCompletion#complete(de.uka.
     * ilkd.key.rule.join.JoinProcedure, de.uka.ilkd.key.proof.Goal)
     */
    @Override
    public JoinWithPredicateAbstraction complete(
            JoinWithPredicateAbstraction proc,
            Pair<Goal, PosInOccurrence> joinGoalPio,
            Collection<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> partners) {
        final Services services = joinGoalPio.first.proof().getServices();

        // Compute the program variables that are different in the
        // respective states.

        final SymbolicExecutionState joinState =
                JoinRuleUtils.sequentToSEPair(joinGoalPio.first.node(),
                        joinGoalPio.second, services);

        final ImmutableList<SymbolicExecutionState> partnerStates =
                JoinRuleUtils.sequentsToSEPairs(partners);

        final ArrayList<LocationVariable> differingLocVars =
                new ArrayList<LocationVariable>();

        JoinRuleUtils
                .getUpdateLeftSideLocations(joinState.first)
                .forEach(v -> {
                    // The meaning of the following statement corresponds to
                    // partnerStates.fold("right value for v differs", false)
                        final boolean isDifferent =
                                StreamSupport
                                        .stream(partnerStates.spliterator(),
                                                false)
                                        .collect(
                                                Collectors
                                                        .reducing(
                                                                false,
                                                                partner -> !JoinRuleUtils
                                                                        .getUpdateRightSideFor(
                                                                                partner.getSymbolicState(),
                                                                                v)
                                                                        .equals(JoinRuleUtils
                                                                                .getUpdateRightSideFor(
                                                                                        joinState
                                                                                                .getSymbolicState(),
                                                                                        v)),
                                                                (b1, b2) -> (b1 || b2)));

                        if (isDifferent) {
                            differingLocVars.add(v);
                        }
                    });

        final AbstractionPredicatesChoiceDialog dialog =
                new AbstractionPredicatesChoiceDialog(joinGoalPio.first,
                        differingLocVars);

        assert proc instanceof JoinWithPredicateAbstractionFactory : "Exptected an procedure of type JoinWithPredicateAbstractionFactory.";

        final JoinWithPredicateAbstractionFactory procF =
                (JoinWithPredicateAbstractionFactory) proc;

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
