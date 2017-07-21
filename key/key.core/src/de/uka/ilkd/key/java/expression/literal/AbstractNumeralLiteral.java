package de.uka.ilkd.key.java.expression.literal;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.expression.Literal;

public abstract class AbstractNumeralLiteral extends Literal {

    protected boolean surroundedByUnaryMinus;
    
    public AbstractNumeralLiteral() {
    }
    
    public AbstractNumeralLiteral(ExtList children) {
	super(children);
    }

    public boolean isSurroundedByUnaryMinus() {
	return surroundedByUnaryMinus;
    }
}
