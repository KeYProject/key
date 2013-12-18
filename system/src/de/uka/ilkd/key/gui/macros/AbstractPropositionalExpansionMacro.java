// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.gui.macros;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.LongRuleAppCost;
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
    protected static Set<String> asSet(String[] strings) {
        return Collections.unmodifiableSet(new LinkedHashSet<String>(Arrays.asList(strings)));
    }

    /**
     * Gets the set of admitted rule names.
     *
     * @return a constant non-<code>null</code> set
     */
    protected abstract Set<String> getAdmittedRuleNames();

    @Override
    protected PropExpansionStrategy createStrategy(KeYMediator mediator, PosInOccurrence posInOcc) {
        return new PropExpansionStrategy(getAdmittedRuleNames());
    }

    /**
     * This strategy accepts all rule apps for which the rule name is in the
     * admitted set and rejects everything else.
     */
    private static class PropExpansionStrategy implements Strategy {

        private static final Name NAME = new Name(PropExpansionStrategy.class.getSimpleName());

        private final Set<String> admittedRuleNames;

        public PropExpansionStrategy(Set<String> admittedRuleNames) {
            this.admittedRuleNames = admittedRuleNames;
        }

        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public RuleAppCost computeCost(RuleApp ruleApp, PosInOccurrence pio, Goal goal) {
            String name = ruleApp.rule().name().toString();
            if(admittedRuleNames.contains(name)) {
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
