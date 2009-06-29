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


public final class IntegerDomainLDT extends AbstractIntegerLDT {
    
    private static final Name NAME = new Name("integerDomain");
    
        
    public IntegerDomainLDT(Namespace sorts, Namespace functions) {
        super((Sort)sorts.lookup(NAME), null, functions);  
    }
    
    
    @Override
    public Name name() {
	return NAME;
    }
    

    @Override
    public Function getAdd() {
	assert false;
        return null;
    }
    
    
    @Override
    public Function getSub() {
	assert false;
        return null;
    }
    
    
    @Override
    public Function getMul() {
	assert false;
        return null;
    }
    
    
    @Override
    public Function getDiv() {
	assert false;
        return null;
    }
    
    
    @Override
    public Function getMod() {
	assert false;
        return null;
    }
    

    @Override
    public Function getShiftLeft() {
	assert false;
        return null;
    }

    
    @Override
    public Function getShiftRight() {
	assert false;
        return null;
    }
    
    
    @Override
    public Function getUnsignedShiftRight() {
	assert false;
        return null;
    }
    
    
    @Override
    public Function getBitwiseOr() {
	assert false;
        return null;
    }
    
    
    @Override
    public Function getBitwiseAnd() {
	assert false;
        return null;
    }
    
    
    @Override
    public Function getBitwiseXor() {
	assert false;
        return null;
    }
    
    
    @Override
    public Function getBitwiseNegation() {
	assert false;
        return null;
    }
    
    
    @Override
    public Function getCast() {
	assert false;
        return null;
    }
    
    
    @Override
    public Function getLessThan() {
	assert false;
        return null;
    }
    
    
    @Override
    public Function getGreaterThan() {
	assert false;
        return null;
    }
    
    
    @Override
    public Function getGreaterOrEquals() {
	assert false;
        return null;
    }
    
    
    @Override
    public Function getLessOrEquals() {
	assert false;
        return null;
    }
    
    
    @Override
    public Function getInBounds() {
	assert false;
        return null;
    }
}
