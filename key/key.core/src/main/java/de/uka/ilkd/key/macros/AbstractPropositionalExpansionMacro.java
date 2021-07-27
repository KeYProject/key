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

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCostCollector;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

/**
 * The Class AbstractPropositionalExpansionMacro applies purely propositional
 * rules.
 *
 * The names of the set of rules to be applied is defined by the abstract method
 * {@link #getAdmittedRuleNames()}.
 *
 * This is very helpful to perform many "andLeft", "impRight" or even "andRight"
 * steps at a time.
 *
 * @author mattias ulbrich
 */
public abstract class AbstractPropositionalExpansionMacro extends StrategyProofMacro {

    /*
     * convert a string array to a set of strings
     */
    protected static Set<String> asSet(String...  strings) {
        return Collections.unmodifiableSet(new LinkedHashSet<String>(Arrays.asList(strings)));
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
        return new PropExpansionStrategy(proof.getActiveStrategy(),
                                         getAdmittedRuleNames(), allowOSS());
    }
    
    /**
     * Checks whether the application of the passed rule is ok in the given
     * context.
     * 
     * @param ruleApp   rule to be applied
     * @param pio       context
     * @param goal      context
     * @return          true if rule may be applied
     */
    protected boolean ruleApplicationInContextAllowed(RuleApp ruleApp, PosInOccurrence pio, Goal goal) {
        return true;
    }

    /**
     * This strategy accepts all rule apps for which the rule name is in the
     * admitted set and rejects everything else.
     */
    private class PropExpansionStrategy implements Strategy {

        private final Name NAME = new Name(PropExpansionStrategy.class.getSimpleName());

        private final Set<String> admittedRuleNames;
        private final Strategy delegate;
        private final boolean allowOSS;

        public PropExpansionStrategy(Strategy delegate, Set<String> admittedRuleNames, boolean allowOSS) {
            this.delegate = delegate;
            this.admittedRuleNames = admittedRuleNames;
            this.allowOSS = allowOSS;
        }

        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public RuleAppCost computeCost(RuleApp ruleApp, PosInOccurrence pio, Goal goal) {
            String name = ruleApp.rule().name().toString();
            if (ruleApp instanceof OneStepSimplifierRuleApp && allowOSS) {
                return delegate.computeCost(ruleApp, pio, goal);
            } else if(admittedRuleNames.contains(name)) {
                final RuleAppCost origCost = delegate.computeCost(ruleApp, pio, goal);
                // pass through negative costs
                if (origCost instanceof NumberRuleAppCost && ((NumberRuleAppCost) origCost).getValue() < 0)
                    return origCost;
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
