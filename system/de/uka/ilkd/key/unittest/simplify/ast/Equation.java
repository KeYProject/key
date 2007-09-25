package de.uka.ilkd.key.unittest.simplify.ast;

public class Equation extends CompFormula{

    public Equation(){
	super("EQ");
    }

    public Equation(Term left, Term right){
	super("EQ", left, right);
    }

}
