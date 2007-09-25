package de.uka.ilkd.key.logic.ldt;

import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.Function;


public class ShortLDT extends AbstractIntegerLDT {
    
    public ShortLDT(Namespace sorts, Namespace functions) {
        super( new Name("jshort"), sorts, functions, PrimitiveType.JAVA_SHORT);   
    }
    
    
    public Function getInBoundsPredicate() {
	return inShort;
    }
}
