package de.uka.ilkd.key.unittest.simplify.ast;

import de.uka.ilkd.key.util.*;

public class Term{

    protected ExtList subs;
    private String op;

    public Term(String op, ExtList subs){
	this.subs = subs;
	this.op = op;
    }

    public Term(String op){
	this(op, new ExtList());
    }

    public int arity(){
	return subs.size();
    }

    public Term sub(int i){
	return (Term) subs.get(i);
    }

    public void setSub(int i, Term t){
//	subs.remove(i);
	subs.add(i, t);
    }

    public void addSub(Term t){
	subs.add(t);	
    }

    public void remove(Term t){
	subs.remove(t);
    }

    public String toSimplify(){
	String result="(" + op;
	for(int i=0; i<arity(); i++){
	    result+=" "+sub(i).toSimplify();
	}
	result+=")";
	return result;
    }

    public String toString(){
	return toSimplify();
    }

    public String op(){
	return op;
    }

}
