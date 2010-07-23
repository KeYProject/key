package de.uka.ilkd.key.rule.updatesimplifier;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rtsj.logic.op.WorkingSpaceNonRigidOp;
import de.uka.ilkd.key.rule.AbstractUpdateRule;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.util.Debug;

public class ApplyOnWorkingSpaceNonRigid extends AbstractUpdateRule {
    
    public ApplyOnWorkingSpaceNonRigid(UpdateSimplifier updateSimplifier) {
        super(updateSimplifier);   
    }

    public boolean isApplicable(Update update, Term target) {
        return target.op() instanceof WorkingSpaceNonRigidOp;   
    }

    public Term apply(Update update, Term target, Services services) {
        return update.getAllAssignmentPairs().size() == 0   ? 
                target : UpdateSimplifierTermFactory.DEFAULT
                        .createUpdateTerm(update.getAllAssignmentPairs(), target);  
    }

    public Term matchingCondition(Update update, Term target, Services services) {
        Debug.fail ( "Don't know how to handle workingSpaceNonRigidOp "
                + target);
        return null;
    }

}
