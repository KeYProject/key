package de.uka.ilkd.key.logic.ldt;

import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.Function;


public class IntLDT extends AbstractIntegerLDT {

    public IntLDT(Namespace sorts, Namespace functions) {
        super(new Name("jint"), sorts, functions, PrimitiveType.JAVA_INT);
    }
    
    
    public Function getInBoundsPredicate() {
	return inInt;
    }
}
