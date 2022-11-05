package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;

public class PrintTermFeature implements TermFeature {

    public static final TermFeature INSTANCE = new PrintTermFeature();

    private PrintTermFeature() {}

    public RuleAppCost compute(Term term, Services services) {
        return NumberRuleAppCost.getZeroCost();
    }
}
