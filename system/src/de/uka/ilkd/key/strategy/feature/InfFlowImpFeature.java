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
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.InfFlowTaclet;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.LongRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;


public class InfFlowImpFeature implements Feature {

    public static final Feature INSTANCE = new InfFlowImpFeature();


    protected InfFlowImpFeature() {
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
            return LongRuleAppCost.ZERO_COST;
        }

        final Term focusFor = pos.constrainedFormula().formula();
        ImmutableList<Term> contractAppls =
                goal.getStrategyInfo(InfFlowTaclet.INF_FLOW_CONTRACT_APPL_PROPERTY);
        if (contractAppls == null) {
            return TopRuleAppCost.INSTANCE;
        }

        for (Term appl : contractAppls) {
            if (isSubFormula(focusFor, appl)) {
                return LongRuleAppCost.ZERO_COST;
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


    private class SubFormulaVisitor extends Visitor {

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
