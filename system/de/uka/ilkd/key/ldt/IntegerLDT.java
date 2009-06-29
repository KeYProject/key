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

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;


public final class IntegerLDT extends AbstractIntegerLDT {
    
    private static final Name NAME = new Name("int");
    
      
    public IntegerLDT(Namespace sorts, Namespace functions) {
        super((Sort)sorts.lookup(NAME), null, functions);
    }
    
    
    @Override
    public Name name() {
	return NAME;
    }

    
    @Override
    public Function getAdd() {
        return plus;
    }
    
    
    @Override
    public Function getSub() {
        return minus;
    }
    
    
    @Override
    public Function getMul() {
        return times;
    }
    
    
    @Override
    public Function getDiv() {
        return divide;
    }
    
    
    @Override
    public Function getMod() {
        return modulo;
    }
    
    
    @Override
    public Function getShiftRight() {
        return null;
    }
    

    @Override
    public Function getShiftLeft() {
        return null;
    }

    
    @Override
    public Function getUnsignedShiftRight() {
        return null;
    }
    
    
    @Override
    public Function getBitwiseOr() {
        return null;
    }
    
    
    @Override
    public Function getBitwiseAnd() {
        return null;
    }
    
    
    @Override
    public Function getBitwiseXor() {
        return null;
    }
    
    
    @Override
    public Function getBitwiseNegation() {
        return null;
    }
    
    
    @Override
    public Function getCast() {
        return null;
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
        return null;
    }
}
