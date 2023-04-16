package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.ExtList;

import java.util.List;

/**
 * Minus assignment.
 */

public class MinusAssignment extends Assignment {

    /**
     * Minus assignment.
     *
     * @param children an ExtList with all children of this node the first children in list will be
     *                 the one on the left side, the second the one on the right side.
     */

    public MinusAssignment(ExtList children) {
        super(children);
    }

    public MinusAssignment(PositionInfo pi, List<Comment> c, Expression target, Expression expr) {
        super(pi, c, target, expr);
    }


    /**
     * Get arity.
     *
     * @return the int value.
     */

    public int getArity() {
        return 2;
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 13;
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
        v.performActionOnMinusAssignment(this);
    }
}
