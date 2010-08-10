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

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.Function;


public class IntegerLDT extends AbstractIntegerLDT {
      
    public IntegerLDT(Namespace sorts, Namespace functions) {
        super(new Name("int"), sorts, functions, null);
    }
    
    
    public Function getAdd() {
        return plus;
    }
    
    
    public Function getSub() {
        return minus;
    }
    
    
    public Function getMul() {
        return times;
    }
    
    
    public Function getDiv() {
        return divide;
    }
    
    
    public Function getMod() {
        return modulo;
    }
    
    
    public Function getShiftRight() {
        return null;
    }
    

    public Function getShiftLeft() {
        return null;
    }

    
    public Function getUnsignedShiftRight() {
        return null;
    }
    
    
    public Function getBitwiseOr() {
        return null;
    }
    
    
    public Function getBitwiseAnd() {
        return null;
    }
    
    
    public Function getBitwiseXor() {
        return null;
    }
    
    
    public Function getBitwiseNegation() {
        return null;
    }
    
    
    public Function getCast() {
        return null;
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
        return null;
    }
}
