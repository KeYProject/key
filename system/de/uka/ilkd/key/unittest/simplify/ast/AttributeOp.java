package de.uka.ilkd.key.unittest.simplify.ast;

public class AttributeOp extends Function{

    protected String attr, className;

    public AttributeOp(String className, String attr){
	super("|."+className+"::"+attr+"|");
	this.className = className;
	this.attr = attr;
    }

    public AttributeOp(String s){
	super(s);
    }

    public String getClassName(){
	return className;
    }

    public String getAttribute(){
	return attr;
    }

}
