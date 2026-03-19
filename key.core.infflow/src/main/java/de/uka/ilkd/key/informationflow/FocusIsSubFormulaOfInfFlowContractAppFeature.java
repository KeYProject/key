/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow;

import de.uka.ilkd.key.informationflow.rule.executor.InfFlowContractAppTacletExecutor;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.equality.RenamingTermProperty;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;



/**
 * Checks whether the focus of the ruleApp is contained in one of the formulas added by information
 * flow contract applications. The list of formulas added by information flow contract applications
 * is retrieved form the strategy property INF_FLOW_CONTRACT_APPL_PROPERTY.
 *
 * @author christoph
 */
public class FocusIsSubFormulaOfInfFlowContractAppFeature implements Feature {

    public static final Feature INSTANCE = new FocusIsSubFormulaOfInfFlowContractAppFeature();


    protected FocusIsSubFormulaOfInfFlowContractAppFeature() {
    }


    @Override
    public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp ruleApp,
            PosInOccurrence pos, Goal p_goal, MutableState mState) {
        assert pos != null : "Feature is only applicable to rules with find.";
        assert ruleApp instanceof TacletApp : "Feature is only applicable " + "to Taclets.";
        TacletApp app = (TacletApp) ruleApp;

        if (!app.assumesInstantionsComplete()) {
            return NumberRuleAppCost.getZeroCost();
        }

        final Term focusFor = pos.sequentFormula().formula();
        final var goal = (de.uka.ilkd.key.proof.Goal) p_goal;
        ImmutableList<JTerm> contractAppls =
            goal.getStrategyInfo(InfFlowContractAppTacletExecutor.INF_FLOW_CONTRACT_APPL_PROPERTY);
        if (contractAppls == null) {
            return TopRuleAppCost.INSTANCE;
        }

        for (Term appl : contractAppls) {
            if (isSubFormula(focusFor, appl)) {
                return NumberRuleAppCost.getZeroCost();
            }
        }

        return TopRuleAppCost.INSTANCE;
    }


    private boolean isSubFormula(Term f1, Term f2) {
        SubFormulaVisitor v = new SubFormulaVisitor(f1);
        f2.execPreOrder(v);
        return v.getIsSubFormula();
    }


    private static class SubFormulaVisitor implements DefaultVisitor {

        final Term potentialSub;

        boolean isSubFormula = false;


        public SubFormulaVisitor(Term potentialSub) {
            this.potentialSub = potentialSub;
        }


        @Override
        public void visit(Term visited) {
            isSubFormula |= RenamingTermProperty.RENAMING_TERM_PROPERTY
                    .equalsModThisProperty(visited, potentialSub);
        }


        boolean getIsSubFormula() {
            return isSubFormula;
        }
    }

}
