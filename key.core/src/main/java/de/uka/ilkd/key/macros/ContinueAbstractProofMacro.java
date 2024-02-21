package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.*;
import de.uka.ilkd.key.strategy.feature.MutableState;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class ContinueAbstractProofMacro extends StrategyProofMacro {
	@Override
    public String getName() {
        return "Continue abstract proof";
    }

    @Override
    public String getCategory() {
        return null;
    }

    @Override
    public String getDescription() {
        return "Continue atomatic rule application using abstract method calls and abstract class invariants.";
    }

    @Override
    protected Strategy createStrategy(Proof proof, PosInOccurrence posInOcc) {
        return new ContinueAbstractProofStrategy(proof.getActiveStrategy(), proof.getSettings().getStrategySettings().getActiveStrategyProperties());
    }
    
    private static class ContinueAbstractProofStrategy implements Strategy {
    	private final Strategy delegate;
        private static final Name NAME = new Name(ContinueAbstractProofStrategy.class.getSimpleName());

        public List<String> forbiddenRuleSets;
        public List<String> forbiddenRules;
        public boolean firstOrderGoalsForbidden;

        public ContinueAbstractProofStrategy(Strategy delegate, StrategyProperties strategyProperties) {
            this.delegate = delegate;
            this.forbiddenRuleSets = Arrays.stream(strategyProperties.getProperty(StrategyProperties.ABSTRACT_PROOF_FORBIDDEN_RULE_SETS)
                    .split(","))
                    .map(String::trim)
                    .filter(str -> !str.isEmpty())
                    .collect(Collectors.toList());
            this.forbiddenRules = Arrays.stream(strategyProperties.getProperty(StrategyProperties.ABSTRACT_PROOF_FORBIDDEN_RULES)
                    .split(","))
                    .map(String::trim)
                    .filter(str -> !str.isEmpty())
                    .collect(Collectors.toList());
            this.firstOrderGoalsForbidden = strategyProperties.getProperty(StrategyProperties.ABSTRACT_PROOF_FIRST_ORDER_GOALS_FORBIDDEN).equals("true");
        }

        /*
         * find a modality term in a node
         */
        private static boolean hasModality(Node node) {
            Sequent sequent = node.sequent();
            for (SequentFormula sequentFormula : sequent) {
                if(hasModality(sequentFormula.formula())) {
                    return true;
                }
            }

            return false;
        }

        /*
         * recursively descent into the term to detect a modality.
         */
        private static boolean hasModality(Term term) {
            if(term.op() instanceof Modality) {
                return true;
            }

            for (Term sub : term.subs()) {
                if(hasModality(sub)) {
                    return true;
                }
            }

            return false;
        }

        @Override
        public Name name() {
            return NAME;
        }

        private boolean isInForbiddenRuleSet(RuleApp ruleApp, String ruleSetName) {
            return ((TacletApp)ruleApp).taclet().getRuleSets().contains(new RuleSet(new Name(ruleSetName)));
        }

        private boolean isInForbiddenRuleSet(RuleApp ruleApp) {
            return forbiddenRuleSets.stream().anyMatch(ruleSetName -> isInForbiddenRuleSet(ruleApp, ruleSetName));
        }

        private boolean isForbiddenRule(RuleApp ruleApp, String ruleName) {
            return ruleApp.rule().name().toString().toLowerCase().startsWith(ruleName.toLowerCase());
        }

        private boolean isForbiddenRule(RuleApp ruleApp) {
            return forbiddenRules.stream().anyMatch(ruleName -> isForbiddenRule(ruleApp, ruleName));
        }

        @Override
        public RuleAppCost computeCost(RuleApp ruleApp, PosInOccurrence pio, Goal goal, MutableState mstate) {
            if (ruleApp instanceof TacletApp &&
                    (isInForbiddenRuleSet(ruleApp) ||
                            (firstOrderGoalsForbidden && !hasModality(goal.node())) ||
                            isForbiddenRule(ruleApp)))
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
        }

        @Override
        public boolean isStopAtFirstNonCloseableGoal() {
            return false;
        }
    }

}
