// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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


public class IntegerDomainLDT extends AbstractIntegerLDT {
        
    public IntegerDomainLDT(Namespace sorts, Namespace functions) {
        super(new Name("integerDomain"), sorts, functions, null);  
    }

    public Function getAdd() {
        return null;
    }
    
    
    public Function getSub() {
        return null;
    }
    
    
    public Function getMul() {
        return null;
    }
    
    
    public Function getDiv() {
        return null;
    }
    
    
    public Function getMod() {
        return null;
    }
    

    public Function getShiftLeft() {
        return null;
    }

    
    public Function getShiftRight() {
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
        return null;
    }
    
    
    public Function getGreaterThan() {
        return null;
    }
    
    
    public Function getGreaterOrEquals() {
        return null;
    }
    
    
    public Function getLessOrEquals() {
        return null;
    }
    
    
    public Function getInBounds() {
        return null;
    }
}
