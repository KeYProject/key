package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.*;
import de.uka.ilkd.key.strategy.feature.MutableState;

public class CompleteAbstractProofMacro extends StrategyProofMacro {
	@Override
    public String getName() {
        return "Complete abstract proof";
    }

    @Override
    public String getCategory() {
        return null;
    }

    @Override
    public String getDescription() {
        return "Finish atomatic rule application using abstract method calls and abstract class invariants.";
    }

    @Override
    protected Strategy createStrategy(Proof proof, PosInOccurrence posInOcc) {
        return new CompleteAbstractProofStrategy(proof.getActiveStrategy());
    }
    
    private static class CompleteAbstractProofStrategy implements Strategy {
    	private final Strategy delegate;
        private static final Name NAME = new Name(CompleteAbstractProofStrategy.class.getSimpleName());

        public CompleteAbstractProofStrategy(Strategy delegate) {
            this.delegate = delegate;
        }

        @Override
        public Name name() {
            return NAME;
        }

        private boolean isForbiddenRule(RuleApp ruleApp) {
            return ruleApp.rule().name().toString().toLowerCase().startsWith("definition_axiom");
        }

        @Override
        public RuleAppCost computeCost(RuleApp ruleApp, PosInOccurrence pio, Goal goal, MutableState mstate) {
            if (ruleApp instanceof TacletApp && isForbiddenRule(ruleApp))
                return TopRuleAppCost.INSTANCE;
            else
                return delegate.computeCost(ruleApp, pio, goal, mstate);
        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
            return delegate.isApprovedApp(app, pio, goal);
        }

        @Override
        public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
                RuleAppCostCollector collector) {
            delegate.instantiateApp(app, pio, goal, collector);
        }

        @Override
        public boolean isStopAtFirstNonCloseableGoal() {
            return delegate.isStopAtFirstNonCloseableGoal();
        }
    }

}
