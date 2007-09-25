package de.uka.ilkd.key.logic.ldt;

import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.Function;


public class ByteLDT extends AbstractIntegerLDT {
    
    public ByteLDT(Namespace sorts, Namespace functions) {
        super(new Name("jbyte"), sorts, functions, PrimitiveType.JAVA_BYTE);
    }
    
    
    public Function getInBoundsPredicate() {
	return inByte;
    }
}
