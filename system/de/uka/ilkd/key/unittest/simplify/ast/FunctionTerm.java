// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest.simplify.ast;

import de.uka.ilkd.key.util.ExtList;

public class FunctionTerm extends Term{

    protected Function f;

    public FunctionTerm(Function f, ExtList l){
	super(f.name(), l);
	this.f = f;
    }

    public FunctionTerm(Function f){
	this(f, new ExtList());
    }

    public Function getFunction(){
	return f;
    }

    public boolean isDivision(){
	return arity()==2 && f.name().startsWith("div_");
    }

    public boolean isArithmetic(){
	return isDivision() || f==Function.PLUS || f==Function.MINUS || 
	    f==Function.MUL;
    }

}
