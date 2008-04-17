package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.logic.Term;

public interface IWorkingSpaceOp {

    Term getMethodTerm(Term t);
    
    ProgramMethod getProgramMethod();
    
    ListOfTerm getParameters(Term t);
    
    Term getSelf(Term t);

}