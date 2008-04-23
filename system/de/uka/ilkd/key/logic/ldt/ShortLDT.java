// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
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


public class ShortLDT extends AbstractIntegerLDT {
    
    public ShortLDT(Namespace sorts, Namespace functions) {
        super( new Name("jshort"), sorts, functions, PrimitiveType.JAVA_SHORT);   
    }
    
    
    
    public Function getAdd() {
        return javaAddInt;
    }
    
    
    public Function getSub() {
        return javaSubInt;
    }
    
    
    public Function getMul() {
        return javaMulInt;
    }
    
    
    public Function getDiv() {
        return javaDivInt;
    }
    
    
    public Function getMod() {
        return javaMod;
    }
    

    public Function getShiftLeft() {
        return javaShiftLeftInt;
    }

    
    public Function getShiftRight() {
        return javaShiftRightInt;
    }
    
    
    public Function getUnsignedShiftRight() {
        return javaUnsignedShiftRightInt;
    }
    
    
    public Function getBitwiseOr() {
        return javaBitwiseOrInt;
    }
    
    
    public Function getBitwiseAnd() {
        return javaBitwiseAndInt;
    }
    
    
    public Function getBitwiseXor() {
        return javaBitwiseXOrInt;
    }
    
    
    public Function getBitwiseNegation() {
        return javaBitwiseNegation;
    }
    
    
    public Function getCast() {
        return javaCastShort;
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
        return inShort;
    }}
