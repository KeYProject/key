package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.Term;

public interface IWorkingSpaceOp {

    Term getMethodTerm(Term t);
    
    ProgramMethod getProgramMethod();
    
    ImmutableList<Term> getParameters(Term t);
    
    Term getSelf(Term t);

}