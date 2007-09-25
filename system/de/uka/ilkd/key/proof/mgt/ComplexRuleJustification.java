package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.RuleApp;

public interface ComplexRuleJustification extends RuleJustification {
    
    public RuleJustification getSpecificJustification(RuleApp app, Services services);
    
}
