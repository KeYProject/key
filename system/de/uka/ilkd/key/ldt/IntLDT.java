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


public final class IntLDT extends AbstractIntegerLDT {
    
    private static final Name NAME = new Name("jint");


    public IntLDT(Namespace sorts, Namespace functions) {
        super((Sort)sorts.lookup(NAME), PrimitiveType.JAVA_INT, functions);
    }
    
    
    @Override
    public Name name() {
	return NAME;
    }    
    
    
    @Override
    public Function getAdd() {
        return javaAddInt;
    }
    
    
    @Override
    public Function getSub() {
        return javaSubInt;
    }
    
    
    @Override
    public Function getMul() {
        return javaMulInt;
    }
    
    
    @Override
    public Function getDiv() {
        return javaDivInt;
    }
    
    
    @Override
    public Function getMod() {
        return javaMod;
    }
    

    @Override
    public Function getShiftLeft() {
        return javaShiftLeftInt;
    }

    
    @Override
    public Function getShiftRight() {
        return javaShiftRightInt;
    }
    
    
    @Override
    public Function getUnsignedShiftRight() {
        return javaUnsignedShiftRightInt;
    }
    
    
    @Override
    public Function getBitwiseOr() {
        return javaBitwiseOrInt;
    }
    
    
    @Override
    public Function getBitwiseAnd() {
        return javaBitwiseAndInt;
    }
    
    
    @Override
    public Function getBitwiseXor() {
        return javaBitwiseXOrInt;
    }
    
    
    @Override
    public Function getBitwiseNegation() {
        return javaBitwiseNegation;
    }
    
    
    @Override
    public Function getCast() {
        return javaCastInt;
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
        return inInt;
    }
}
