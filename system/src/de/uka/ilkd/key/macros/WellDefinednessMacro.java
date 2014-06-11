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

package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.WellDefinednessPO;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.WellDefinednessCheck;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCostCollector;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

/**
 * This macro resolves the well-definedness transformer, i.e. it applies exactly
 * all applicable rules to resolve the operators WD and wd (which are formula/term
 * transformers). These rules all have the prefix defined in {@link #WD_PREFIX}.
 * The macro is only applicable for proof obligations created in {@link #WellDefinednessPO}
 * and the Well-Definedness branches in {@link #WhileInvariantRule} and {@link #BlockContractRule}.
 *
 * @author Michael Kirsten
 */
public class WellDefinednessMacro extends StrategyProofMacro {

    public static final String WD_PREFIX = "wd_";
    public static final String WD_BRANCH = "Well-Definedness";

    @Override
    public String getName() {
        return "Well-Definedness Rules";
    }

    @Override
    public String getDescription() {
        return "Apply only rules to resolve the Well-Definedness transformer.";
    }

    @Override
    protected Strategy createStrategy(KeYMediator mediator,
                                      PosInOccurrence posInOcc) {
        return new WellDefinednessStrategy();
    }

    @Override
    public boolean canApplyTo(KeYMediator mediator, ImmutableList<Goal> goals, PosInOccurrence posInOcc) {
        final Proof proof = mediator.getSelectedProof();
        if (proof == null
                || mediator.getServices() == null
                || mediator.getServices().getSpecificationRepository() == null
                || !WellDefinednessCheck.isOn()) {
            return false;
        }
        final ContractPO po = mediator.getServices().getSpecificationRepository().getPOForProof(proof);
        if (po instanceof WellDefinednessPO) { // applicable for all well-definedness checks
            return true;
        }
        if (!(po instanceof FunctionalOperationContractPO)) {
            return false;
        }
        for (Goal goal: goals) {
            Node n = goal.node();
            while (n != null) {
                // Applicable in a well-definedness branch (e.g. of a loop statement or a block contract)
                if (n.getNodeInfo().getBranchLabel() != null
                        && n.getNodeInfo().getBranchLabel().equals(WD_BRANCH)) {
                    return true;
                }
                n = n.parent();
            }
        }        
        return false;
    }

    /**
     * This strategy accepts all rule apps for which the rule name is a
     * Well-Definedness rule and rejects everything else.
     */
    private static class WellDefinednessStrategy implements Strategy {

        private static final Name NAME = new Name(WellDefinednessStrategy.class.getSimpleName());

        public WellDefinednessStrategy() {
        }

        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public RuleAppCost computeCost(RuleApp ruleApp, PosInOccurrence pio, Goal goal) {
            String name = ruleApp.rule().name().toString();
            if(name.startsWith(WD_PREFIX)) {
                return NumberRuleAppCost.getZeroCost();
            } else {
                return TopRuleAppCost.INSTANCE;
            }
        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
            return true;
        }

        @Override
        public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
                RuleAppCostCollector collector) {
        }
    }
}