package de.uka.ilkd.key.unittest.simplify.ast;

public class ArrayLength extends AttributeOp{

    public ArrayLength(String length){
	super(length);
	this.className = null;
	this.attr = length;
    }

}
