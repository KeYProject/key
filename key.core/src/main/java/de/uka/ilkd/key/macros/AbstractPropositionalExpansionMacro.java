/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.*;
import de.uka.ilkd.key.strategy.feature.MutableState;

import org.key_project.logic.Name;

/**
 * The Class AbstractPropositionalExpansionMacro applies purely propositional rules.
 *
 * The names of the set of rules to be applied is defined by the abstract method
 * {@link #getAdmittedRuleNames()}.
 *
 * This is very helpful to perform many "andLeft", "impRight" or even "andRight" steps at a time.
 *
 * @author mattias ulbrich
 */
public abstract class AbstractPropositionalExpansionMacro extends StrategyProofMacro {

    /*
     * convert a string array to a set of strings
     */
    protected static Set<String> asSet(String... strings) {
        return Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(strings)));
    }

    @Override
    public String getCategory() {
        return "Propositional";
    }

    /**
     * Gets the set of admitted rule names.
     *
     * @return a constant non-<code>null</code> set
     */
    protected abstract Set<String> getAdmittedRuleNames();

    /**
     * Whether this macro includes One Step Simplification.
     */
    protected abstract boolean allowOSS();

    @Override
    protected Strategy createStrategy(Proof proof, PosInOccurrence posInOcc) {
        return new PropExpansionStrategy(proof.getActiveStrategy(), getAdmittedRuleNames(),
            allowOSS());
    }

    /**
     * Checks whether the application of the passed rule is ok in the given context.
     *
     * @param ruleApp rule to be applied
     * @param pio context
     * @param goal context
     * @return true if rule may be applied
     */
    protected boolean ruleApplicationInContextAllowed(RuleApp ruleApp, PosInOccurrence pio,
            Goal goal) {
        return true;
    }

    /**
     * This strategy accepts all rule apps for which the rule name is in the admitted set and
     * rejects everything else.
     */
    private static class PropExpansionStrategy implements Strategy {

        private final Name NAME = new Name(PropExpansionStrategy.class.getSimpleName());

        private final Set<String> admittedRuleNames;
        private final Strategy delegate;
        private final boolean allowOSS;

        public PropExpansionStrategy(Strategy delegate, Set<String> admittedRuleNames,
                boolean allowOSS) {
            this.delegate = delegate;
            this.admittedRuleNames = admittedRuleNames;
            this.allowOSS = allowOSS;
        }

        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public RuleAppCost computeCost(RuleApp ruleApp, PosInOccurrence pio, Goal goal,
                MutableState mState) {
            String name = ruleApp.rule().name().toString();
            if (ruleApp instanceof OneStepSimplifierRuleApp && allowOSS) {
                return delegate.computeCost(ruleApp, pio, goal, mState);
            } else if (admittedRuleNames.contains(name)) {
                final RuleAppCost origCost = delegate.computeCost(ruleApp, pio, goal, mState);
                // pass through negative costs
                if (origCost instanceof NumberRuleAppCost
                        && ((NumberRuleAppCost) origCost).getValue() < 0) {
                    return origCost;
                }
                // cap costs at zero
                return NumberRuleAppCost.getZeroCost();
            } else {
                return TopRuleAppCost.INSTANCE;
            }
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
