// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.logic.ldt;

import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.Function;


public class LongLDT extends AbstractIntegerLDT {
    
    public LongLDT(Namespace sorts, Namespace functions) {
        super(new Name("jlong"), sorts, functions, PrimitiveType.JAVA_LONG);        
    }
    
  
    public Function getAdd() {
        return javaAddLong;
    }
    
    
    public Function getSub() {
        return javaSubLong;
    }
    
    
    public Function getMul() {
        return javaMulLong;
    }
    
    
    public Function getDiv() {
        return javaDivLong;
    }
    
    
    public Function getMod() {
        return javaMod;
    }
    

    public Function getShiftLeft() {
        return javaShiftLeftLong;
    }

    
    public Function getShiftRight() {
        return javaShiftRightLong;
    }
    
    
    public Function getUnsignedShiftRight() {
        return javaUnsignedShiftRightLong;
    }
    
    
    public Function getBitwiseOr() {
        return javaBitwiseOrLong;
    }
    
    
    public Function getBitwiseAnd() {
        return javaBitwiseAndLong;
    }
    
    
    public Function getBitwiseXor() {
        return javaBitwiseXOrLong;
    }
    
    
    public Function getBitwiseNegation() {
        return javaBitwiseNegation;
    }
    
    
    public Function getCast() {
        return javaCastLong;
    }
    
    
    public Function getLessThan() {
        return lessThan;
    }
    
    
    public Function getGreaterThan() {
        return greaterThan;
    }
    
    
    public Function getGreaterOrEquals() {
        return greaterOrEquals;
    }
    
    
    public Function getLessOrEquals() {
        return lessOrEquals;
    }
    
    
    public Function getInBounds() {
        return inLong;
    }
}
