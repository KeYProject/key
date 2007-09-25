package de.uka.ilkd.key.logic.ldt;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.Function;


public class IntegerLDT extends AbstractIntegerLDT {
      
    public IntegerLDT(Namespace sorts, Namespace functions) {
        super(new Name("int"), sorts, functions, null);
    }
    

    public Function getInBoundsPredicate() {
	return null;
    }
}
