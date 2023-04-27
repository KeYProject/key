package de.uka.ilkd.key.java.expression.operator;

import java.util.List;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * Pre increment.
 */

public class PreIncrement extends Assignment {


    /**
     * Pre increment.
     *
     * @param children an ExtList with all children of this node
     */

    public PreIncrement(ExtList children) {
        super(children);
    }

    public PreIncrement(PositionInfo pi, List<Comment> c, Expression child) {
        super(pi, c, child);
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
        return PREFIX;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnPreIncrement(this);
    }
}
