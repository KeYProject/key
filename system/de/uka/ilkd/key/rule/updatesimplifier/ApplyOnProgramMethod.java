package de.uka.ilkd.key.rule.updatesimplifier;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.rule.UpdateSimplifier;

public class ApplyOnProgramMethod extends ApplyOnModality {

    public ApplyOnProgramMethod(UpdateSimplifier updateSimplifier, 
            boolean deletionEnabled) {
        super(updateSimplifier, deletionEnabled);        
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.IUpdateRule#isApplicable(de.uka.ilkd.key.rule.updatesimplifier.Update, de.uka.ilkd.key.logic.Term)
     */
    public boolean isApplicable(Update update, Term target) {                
        return target.op() instanceof ProgramMethod;         
    }

   
}
