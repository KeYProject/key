package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.rule.RuleApp;

public interface ComplexRuleJustification extends RuleJustification {

    RuleJustification getSpecificJustification(RuleApp app, TermServices services);

}
