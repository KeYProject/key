// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;


public final class LongLDT extends AbstractIntegerLDT {
    
    private static final Name NAME = new Name("jlong");
    
    
    public LongLDT(Namespace sorts, Namespace functions) {
        super((Sort)sorts.lookup(NAME), PrimitiveType.JAVA_LONG, functions);        
    }
    
    
    @Override
    public Name name() {
	return NAME;
    }
     
     
    @Override
    public Function getAdd() {
        return javaAddLong;
    }
    
    
    @Override
    public Function getSub() {
        return javaSubLong;
    }
    
    
    @Override
    public Function getMul() {
        return javaMulLong;
    }
    
    
    @Override
    public Function getDiv() {
        return javaDivLong;
    }
    
    
    @Override
    public Function getMod() {
        return javaMod;
    }
    

    @Override
    public Function getShiftLeft() {
        return javaShiftLeftLong;
    }

    
    @Override
    public Function getShiftRight() {
        return javaShiftRightLong;
    }
    
    
    @Override
    public Function getUnsignedShiftRight() {
        return javaUnsignedShiftRightLong;
    }
    
    
    @Override
    public Function getBitwiseOr() {
        return javaBitwiseOrLong;
    }
    
    
    @Override
    public Function getBitwiseAnd() {
        return javaBitwiseAndLong;
    }
    
    
    @Override
    public Function getBitwiseXor() {
        return javaBitwiseXOrLong;
    }
    
    
    @Override
    public Function getBitwiseNegation() {
        return javaBitwiseNegation;
    }
    
    
    @Override
    public Function getCast() {
        return javaCastLong;
    }
    
    
    @Override
    public Function getLessThan() {
        return lessThan;
    }
    
    
    @Override
    public Function getGreaterThan() {
        return greaterThan;
    }
    
    
    @Override
    public Function getGreaterOrEquals() {
        return greaterOrEquals;
    }
    
    
    @Override
    public Function getLessOrEquals() {
        return lessOrEquals;
    }
    
    
    @Override
    public Function getInBounds() {
        return inLong;
    }
}
