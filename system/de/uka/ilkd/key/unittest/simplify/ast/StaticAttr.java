package de.uka.ilkd.key.unittest.simplify.ast;

public class StaticAttr extends AttributeOp{

    public StaticAttr(String className, String attr){
	super("|"+className+"::"+attr+"|");
	this.className = className;
	this.attr = attr;
    }

}
