package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * Post increment.
 */

public class PostIncrement extends Assignment {


    /**
     * Post increment.
     *
     * @param unary the Expression to be incremented by one
     */

    public PostIncrement(Expression unary) {
        super(unary);
    }


    /**
     * Post increment.
     *
     * @param children an ExtList with all children of this node
     */

    public PostIncrement(ExtList children) {
        super(children);
    }


    /**
     * Get arity.
     *
     * @return the int value.
     */

    public int getArity() {
        return 1;
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 1;
    }

    /**
     * Get notation.
     *
     * @return the int value.
     */

    public int getNotation() {
        return POSTFIX;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnPostIncrement(this);
    }
}
