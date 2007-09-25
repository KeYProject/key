package de.uka.ilkd.key.rule.updatesimplifier;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.NonRigidHeapDependentFunction;
import de.uka.ilkd.key.rule.UpdateSimplifier;

/**
 * This rule deals with locations that are only heap dependent, i.e. they do not  
 * depend on local program variables.
 */
public class ApplyOnHeapDependentLocation extends ApplyOnModality {
    public ApplyOnHeapDependentLocation(UpdateSimplifier updateSimplifier, 
            boolean deletionEnabled) {
        super(updateSimplifier, deletionEnabled);        
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.IUpdateRule#isApplicable(de.uka.ilkd.key.rule.updatesimplifier.Update, de.uka.ilkd.key.logic.Term)
     */
    public boolean isApplicable(Update update, Term target) {                
        return target.op() instanceof NonRigidHeapDependentFunction;         
    }
}
