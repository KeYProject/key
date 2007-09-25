package de.uka.ilkd.key.logic.ldt;

import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.Function;


public class LongLDT extends AbstractIntegerLDT {
    
    public LongLDT(Namespace sorts, Namespace functions) {
        super(new Name("jlong"), sorts, functions, PrimitiveType.JAVA_LONG);        
    }
    
    
    public Function getInBoundsPredicate() {
	return inLong;
    }
}
