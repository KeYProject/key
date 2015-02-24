// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.InfFlowContractAppTaclet;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;


/**
 * Checks whether the focus of the ruleApp is contained in one of the formulas
 * added by information flow contract applications. The list of formulas
 * added by information flow contract applications is retrieved form the
 * the strategy property INF_FLOW_CONTRACT_APPL_PROPERTY.
 *
 * @author christoph
 */
public class FocusIsSubFormulaOfInfFlowContractAppFeature implements Feature {

    public static final Feature INSTANCE = new FocusIsSubFormulaOfInfFlowContractAppFeature();


    protected FocusIsSubFormulaOfInfFlowContractAppFeature() {
    }


    @Override
    public RuleAppCost compute(RuleApp ruleApp,
                               PosInOccurrence pos,
                               Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find.";
        assert ruleApp instanceof TacletApp : "Feature is only applicable " +
                                              "to Taclets.";
        TacletApp app = (TacletApp) ruleApp;

        if (!app.ifInstsComplete()) {
            return NumberRuleAppCost.getZeroCost();
        }

        final Term focusFor = pos.constrainedFormula().formula();
        ImmutableList<Term> contractAppls =
                goal.getStrategyInfo(InfFlowContractAppTaclet.INF_FLOW_CONTRACT_APPL_PROPERTY);
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


    private boolean isSubFormula(Term f1,
                                 Term f2) {
        SubFormulaVisitor v = new SubFormulaVisitor(f1);
        f2.execPreOrder(v);
        return v.getIsSubFormula();
    }


    private class SubFormulaVisitor extends DefaultVisitor {

        final Term potentialSub;

        boolean isSubFormula = false;


        public SubFormulaVisitor(Term potentialSub) {
            this.potentialSub = potentialSub;
        }


        @Override
        public void visit(Term visited) {
            isSubFormula |= visited.equalsModRenaming(potentialSub);
        }


        boolean getIsSubFormula() {
            return isSubFormula;
        }
    }

}
