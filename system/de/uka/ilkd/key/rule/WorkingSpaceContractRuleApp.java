package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.jml.JMLMethodSpec;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.PosInOccurrence;

public class WorkingSpaceContractRuleApp extends BuiltInRuleApp {

    private JMLMethodSpec spec;
    /**
     * -1 iff the precondition of spec is supposed to be weaker than the 
     * precondition associated with the selected working_space term.
     * 0 iff equivalent
     * 1 iff stronger
     */
    private int compare;
    
    public WorkingSpaceContractRuleApp(UseWorkingSpaceContractRule builtInRule, 
                                 PosInOccurrence pio,
                                 Constraint userConstraint,
                                 JMLMethodSpec spec,
                                 int compare) {
        super(builtInRule, pio, userConstraint);
        this.spec = spec;
        this.compare = compare;
    }   
    
    public JMLMethodSpec getMethodSpec() {
        return spec;
    }
    
    public int compare(){
        return compare;
    }

    
}