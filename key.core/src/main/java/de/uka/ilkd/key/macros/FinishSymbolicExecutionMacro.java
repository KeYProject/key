/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.strategy.Strategy;

/**
 * The macro FinishSymbolicExecutionMacro continues automatic rule application until there is no
 * more modality on the sequent.
 * <p>
 * This is done by implementing a delegation {@link Strategy} which assigns to any rule application
 * infinite costs if there is no modality on the sequent.
 *
 * @author mattias ulbrich
 */
public class FinishSymbolicExecutionMacro extends StrategyProofMacro {

    private static final Name NON_HUMAN_INTERACTION_RULESET = new Name("notHumanReadable");
    private static final Name DELAYED_EXPANSION_RULESET = new Name("delayedExpansion");

    @Override
    public String getName() {
        return "Finish Symbolic Execution";
    }

    @Override
    public String getCategory() {
        return "Auto Pilot";
    }

    @Override
    public String getScriptCommandName() {
        return "symbex";
    }

    @Override
    public String getDescription() {
        return "Continue automatic strategy application until no more modality is on the sequent.";
    }

    /**
     * Checks if a rule is forbidden for symbolic execution macros.
     *
     * @param rule the rule to check
     * @return true if this rule should not be executed by a symbolic execution macro
     */
    public static boolean isForbiddenRule(Rule rule) {
        return isInRuleSet(rule, NON_HUMAN_INTERACTION_RULESET)
                || isInRuleSet(rule, DELAYED_EXPANSION_RULESET);
    }

    private static boolean isInRuleSet(Rule rule, Name ruleSetName) {
        if (rule instanceof Taclet) {
            Taclet taclet = (Taclet) rule;
            for (RuleSet rs : taclet.getRuleSets()) {
                if (ruleSetName.equals(rs.name())) {
                    return true;
                }
            }
        }
        return false;
    }

    @Override
    protected Strategy createStrategy(Proof proof, PosInOccurrence posInOcc) {
        return new FilterSymbexStrategy(proof.getActiveStrategy());
    }

    /**
     * The Class FilterAppManager is a special strategy assigning to any rule infinite costs if the
     * goal has no modality
     */
    private static class FilterSymbexStrategy extends FilterStrategy {

        private static final Name NAME = new Name(FilterSymbexStrategy.class.getSimpleName());

        /**
         * the modality cache used by this strategy
         */
        private final ModalityCache modalityCache = new ModalityCache();

        public FilterSymbexStrategy(Strategy delegate) {
            super(delegate);
        }

        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
            if (!modalityCache.hasModality(goal.node().sequent())) {
                return false;
            }
            if (isForbiddenRule(app.rule())) {
                return false;
            }

            return super.isApprovedApp(app, pio, goal);
        }

        @Override
        public boolean isStopAtFirstNonCloseableGoal() {
            return false;
        }

    }

}
