package de.uka.ilkd.key.macros;

import java.util.*;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCostCollector;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

public class AutoPilotPrepareProofMacro extends StrategyProofMacro {

    private static final String[] ADMITTED_RULES = { "orRight", "impRight", "close", "andRight" };

    private static final Set<String> ADMITTED_RULES_SET = asSet(ADMITTED_RULES);

    private static final Name NON_HUMAN_INTERACTION_RULESET = new Name("notHumanReadable");

    public AutoPilotPrepareProofMacro() { super(); }

    @Override
    public String getName() {
        return "Auto Pilot (Preparation Only)";
    }

    @Override
    public String getCategory() {
        return "Auto Pilot";
    }

    @Override
    public String getDescription() {
        return "<html><ol><li>Finish symbolic execution" + "<li>Separate proof obligations"
            + "<li>Expand invariant definitions</ol>";
    }

    @Override
    public String getScriptCommandName() {
        return "autopilot-prep";
    }

    /*
     * convert a string array to a set of strings
     */
    protected static Set<String> asSet(String[] strings) {
        return Collections.unmodifiableSet(new LinkedHashSet<String>(Arrays.asList(strings)));
    }

    /*
     * Checks if a rule is marked as not suited for interaction.
     */
    private static boolean isNonHumanInteractionTagged(Rule rule) {
        return isInRuleSet(rule, NON_HUMAN_INTERACTION_RULESET);
    }

    private static boolean isInRuleSet(Rule rule, Name ruleSetName) {
        if (rule instanceof Taclet) {
            Taclet taclet = (Taclet) rule;
            for (RuleSet rs : taclet.getRuleSets()) {
                if (ruleSetName.equals(rs.name()))
                    return true;
            }
        }
        return false;
    }

    private static class AutoPilotStrategy implements Strategy {

        private static final Name NAME = new Name("Autopilot filter strategy");
        private final Strategy delegate;
        /** the modality cache used by this strategy */
        private final ModalityCache modalityCache = new ModalityCache();

        public AutoPilotStrategy(Proof proof, PosInOccurrence posInOcc) {
            this.delegate = proof.getActiveStrategy();
        }

        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
            return computeCost(app, pio, goal) != TopRuleAppCost.INSTANCE &&
            // Assumptions are normally not considered by the cost
            // computation, because they are normally not yet
            // instantiated when the costs are computed. Because the
            // application of a rule sometimes makes sense only if
            // the assumptions are instantiated in a particular way
            // (for instance equalities should not be applied on
            // themselves), we need to give the delegate the possiblity
            // to reject the application of a rule by calling
            // isApprovedApp. Otherwise, in particular equalities may
            // be applied on themselves.
                    delegate.isApprovedApp(app, pio, goal);
        }

        @Override
        public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio, Goal goal) {

            Rule rule = app.rule();
            if (isNonHumanInteractionTagged(rule)) {
                return TopRuleAppCost.INSTANCE;
            }

            if (modalityCache.hasModality(goal.node().sequent())) {
                return delegate.computeCost(app, pio, goal);
            }

            String name = rule.name().toString();
            if (ADMITTED_RULES_SET.contains(name)) {
                return NumberRuleAppCost.getZeroCost();
            }

            // apply OSS to <inv>() calls.
            if (rule instanceof OneStepSimplifier) {
                Term target = pio.subTerm();
                if (target.op() instanceof UpdateApplication) {
                    Operator updatedOp = target.sub(1).op();
                    if (updatedOp instanceof ObserverFunction) {
                        return NumberRuleAppCost.getZeroCost();
                    }
                }
            }

            return TopRuleAppCost.INSTANCE;
        }

        @Override
        public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
                RuleAppCostCollector collector) {
            delegate.instantiateApp(app, pio, goal, collector);
        }

        @Override
        public boolean isStopAtFirstNonCloseableGoal() {
            return false;
        }

    }

    @Override
    protected Strategy createStrategy(Proof proof, PosInOccurrence posInOcc) {
        return new AutoPilotStrategy(proof, posInOcc);
    }
}
