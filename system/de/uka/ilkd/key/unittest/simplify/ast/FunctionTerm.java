package de.uka.ilkd.key.unittest.simplify.ast;

import de.uka.ilkd.key.util.*;

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
