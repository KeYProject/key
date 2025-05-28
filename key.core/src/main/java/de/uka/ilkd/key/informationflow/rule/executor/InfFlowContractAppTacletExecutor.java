/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.rule.executor;

import de.uka.ilkd.key.informationflow.rule.InfFlowContractAppTaclet;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.StrategyInfoUndoMethod;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.executor.javadl.RewriteTacletExecutor;
import de.uka.ilkd.key.util.properties.Properties;

import org.key_project.logic.LogicServices;
import org.key_project.prover.rules.instantiation.MatchConditions;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.SequentChangeInfo;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;

public class InfFlowContractAppTacletExecutor extends RewriteTacletExecutor {
    /**
     * Strategy property which saves the list of formulas which where added by information flow
     * contract applications. This list is used by the macros UseInformationFlowContractMacro and
     * PrepareInfFlowContractPreBranchesMacro to decide how to prepare the formulas resulting from
     * information flow contract applications.
     */
    @SuppressWarnings("unchecked")
    public static final Properties.Property<ImmutableList<JTerm>> INF_FLOW_CONTRACT_APPL_PROPERTY =
        new Properties.Property<>(
            (Class<ImmutableList<JTerm>>) (Class<?>) ImmutableList.class,
            "information flow contract applicaton property");


    public InfFlowContractAppTacletExecutor(InfFlowContractAppTaclet taclet) {
        super(taclet);
    }


    /**
     * adds SequentFormula to antecedent depending on position information (if none is handed over
     * it is added at the head of the antecedent). Of course it has to be ensured that the position
     * information describes one occurrence in the antecedent of the sequent.
     *
     * @param semi the Semisequent with the the ConstrainedFormulae to be added
     * @param currentSequent the Sequent which is the current (intermediate) result of applying the
     *        taclet
     * @param pos the PosInOccurrence describing the place in the sequent or null for head of
     *        antecedent
     * @param applicationPosInOccurrence The {@link PosInOccurrence} of the {@link JTerm} which is
     *        rewritten
     * @param matchCond the MatchConditions containing in particular the instantiations of the
     *        schemavariables
     * @param services the Services
     * @param instantiationInfo additional instantiation information concerning label:
     *        <ul>
     *        <li>termLabelState: The {@link TermLabelState} of the current rule application.</li>
     *        <li>labelHint: The hint used to maintain {@link TermLabel}s. the instantiations of the
     *        schemavariables</li>
     *        </ul>
     */
    @Override
    protected void addToAntec(Semisequent semi, SequentChangeInfo currentSequent,
            PosInOccurrence pos, PosInOccurrence applicationPosInOccurrence,
            MatchConditions matchCond, @NonNull Goal goal,
            @NonNull TacletApp tacletApp,
            LogicServices services, Object... instantiationInfo) {

        final ImmutableList<SequentFormula> replacements =
            instantiateSemisequent(semi, pos, matchCond, goal, tacletApp, goal.getOverlayServices(),
                instantiationInfo);
        assert replacements.size() == 1
                : "information flow taclets must have " + "exactly one add!";
        updateStrategyInfo(goal.proof().openEnabledGoals().head(),
            (JTerm) replacements.iterator().next().formula());
        super.addToAntec(semi, currentSequent, pos, applicationPosInOccurrence, matchCond, goal,
            tacletApp, services, instantiationInfo);
    }

    /**
     * Add the contract application formula to the list of the INF_FLOW_CONTRACT_APPL_PROPERTY.
     *
     * @param goal the current goal
     * @param applFormula the information contract application formula added by this taclet
     */
    private void updateStrategyInfo(Goal goal, final JTerm applFormula) {
        ImmutableList<JTerm> applFormulas = goal.getStrategyInfo(INF_FLOW_CONTRACT_APPL_PROPERTY);
        if (applFormulas == null) {
            applFormulas = ImmutableSLList.nil();
        }
        applFormulas = applFormulas.append(applFormula);
        StrategyInfoUndoMethod undo = strategyInfos -> {
            ImmutableList<JTerm> applFormulas1 =
                strategyInfos.get(INF_FLOW_CONTRACT_APPL_PROPERTY);
            strategyInfos.put(INF_FLOW_CONTRACT_APPL_PROPERTY,
                applFormulas1.removeAll(applFormula));
        };
        goal.addStrategyInfo(INF_FLOW_CONTRACT_APPL_PROPERTY, applFormulas, undo);

    }

}
