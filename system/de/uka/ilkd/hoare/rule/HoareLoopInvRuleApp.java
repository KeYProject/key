package de.uka.ilkd.hoare.rule;

import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.BuiltInRuleApp;

public class HoareLoopInvRuleApp extends BuiltInRuleApp {

    private final Term inv;
    
    public HoareLoopInvRuleApp(Term inv, BuiltInRule builtInRule, PosInOccurrence pio, 
            Constraint userConstraint) {
        super(builtInRule, pio, userConstraint);      
        this.inv = inv;
    }

    public Term getInvariant() {
        return inv;
    }


    public String toString() {
        return "Loop invariant rule application";
    }
    
}
