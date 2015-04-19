package de.uka.ilkd.key.informationflow.rule.executor;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.informationflow.rule.InfFlowContractAppTaclet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.StrategyInfoUndoMethod;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;
import de.uka.ilkd.key.rule.executor.javadl.RewriteTacletExecutor;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.properties.Properties;

public class InfFlowContractAppTacletExecutor extends RewriteTacletExecutor<InfFlowContractAppTaclet> {
    /**
     * Strategy property which saves the list of formulas which where added
     * by information flow contract applications. This list is used by the
     * macros UseInformationFlowContractMacro and
     * PrepareInfFlowContractPreBranchesMacro to decide how to prepare the
     * formulas resulting from information flow contract applications.
     */
    @SuppressWarnings("unchecked")
    public static final Properties.Property<ImmutableList<Term>> INF_FLOW_CONTRACT_APPL_PROPERTY =
            new Properties.Property<ImmutableList<Term>>(
                    (Class<ImmutableList<Term>>) (Class<?>) ImmutableList.class,
                     "information flow contract applicaton property");

    
    public InfFlowContractAppTacletExecutor(InfFlowContractAppTaclet taclet) {
        super(taclet);
    }


    @Override
    protected void addToAntec(TermLabelState termLabelState,
            Semisequent semi,
            SequentChangeInfo currentSequent,
            PosInOccurrence pos,
            Services services,
            MatchConditions matchCond,
            PosInOccurrence applicationPosInOccurrence,
            TacletLabelHint labelHint,
            Goal goal,
            TacletApp tacletApp) {
        final ImmutableList<SequentFormula> replacements =
                instantiateSemisequent(termLabelState, semi, services, matchCond, pos, labelHint, goal, tacletApp);
        assert replacements.size() == 1 : "information flow taclets must have " +
                "exactly one add!";
        updateStrategyInfo(services.getProof().openEnabledGoals().head(),
                replacements.iterator().next().formula());
        super.addToAntec(termLabelState, semi, currentSequent, pos, services, matchCond, applicationPosInOccurrence, labelHint, goal, tacletApp);
    }

    /**
     * Add the contract application formula to the list of the
     * INF_FLOW_CONTRACT_APPL_PROPERTY.
     * @param goal          the current goal
     * @param applFormula   the information contract application formula added
     *                      by this taclet
     */
    private void updateStrategyInfo(Goal goal, final Term applFormula) {
        ImmutableList<Term> applFormulas =
                goal.getStrategyInfo(INF_FLOW_CONTRACT_APPL_PROPERTY);
        if (applFormulas == null) {
            applFormulas = ImmutableSLList.<Term>nil();
        }
        applFormulas = applFormulas.append(applFormula);
        StrategyInfoUndoMethod undo = new StrategyInfoUndoMethod() {

            @Override
            public void undo(Properties strategyInfos) {
                ImmutableList<Term> applFormulas =
                        strategyInfos.get(INF_FLOW_CONTRACT_APPL_PROPERTY);
                strategyInfos.put(INF_FLOW_CONTRACT_APPL_PROPERTY, applFormulas.removeAll(applFormula));
            }
        };
        goal.addStrategyInfo(INF_FLOW_CONTRACT_APPL_PROPERTY, applFormulas, undo);

    }

}
