package de.uka.ilkd.key.unittest.simplify.ast;

public class Function{

    public static Function PLUS = new Function("+");
    public static Function MINUS = new Function("-");
    public static Function MUL = new Function("*");

    protected String name;

    public Function(String name){
	this.name = name;
    }

    public String name(){
	return name;
    }
    
    public String toSimplify(){
	return name;
    }

}
