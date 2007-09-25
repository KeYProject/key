package de.uka.ilkd.key.logic.ldt;

import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.Function;


public class CharLDT extends AbstractIntegerLDT {
    
    public CharLDT(Namespace sorts, Namespace functions) {
        super(new Name("jchar"), sorts, functions, PrimitiveType.JAVA_CHAR);
    }
    

    public Function getInBoundsPredicate() {
	return inChar;
    }
}
