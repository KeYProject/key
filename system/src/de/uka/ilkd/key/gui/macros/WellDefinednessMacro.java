package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.WellDefinednessPO;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.LongRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCostCollector;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

public class WellDefinednessMacro extends StrategyProofMacro {

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
    public boolean canApplyTo(KeYMediator mediator, PosInOccurrence posInOcc) {
        final Proof p = mediator.getSelectedProof();
        final SpecificationRepository rep = mediator.getServices().getSpecificationRepository();
        return rep.getPOForProof(p) instanceof WellDefinednessPO;
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
            if(name.startsWith("wd_")) {
                return LongRuleAppCost.ZERO_COST;
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