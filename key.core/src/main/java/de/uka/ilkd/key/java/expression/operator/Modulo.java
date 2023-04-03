package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;


/**
 * Modulo.
 */
public class Modulo extends BinaryOperator {


    /**
     * Modulo.
     */

    public Modulo(ExtList children) {
        super(children);
    }

    public Modulo(Expression lhs, Expression rhs) {
        super(lhs, rhs);
    }



    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 2;
    }

    /**
     * Get notation.
     *
     * @return the int value.
     */

    public int getNotation() {
        return INFIX;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnModulo(this);
    }

}
