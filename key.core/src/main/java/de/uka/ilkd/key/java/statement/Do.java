package de.uka.ilkd.key.java.statement;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.visitor.Visitor;

/**
 * Do.
 *
 */
public class Do extends LoopStatement {

    /**
     * Do.
     */
    public Do() {
        super();
    }

    /**
     * Do.
     *
     * @param guard an expression.
     */
    public Do(Expression guard) {
        super(guard);
    }

    /**
     * Do.
     *
     * @param guard an expression.
     * @param body a statement.
     */
    public Do(Expression guard, Statement body, ExtList l, PositionInfo pos) {
        super(guard, body, l, pos);
    }

    /**
     * Do.
     *
     * @param guard an expression.
     * @param body a statement.
     */
    public Do(Expression guard, Statement body, PositionInfo pos) {
        super(guard, body, pos);
    }

    public SourceElement getLastElement() {
        return this;
    }

    /**
     * Is checked before iteration.
     *
     * @return the boolean value.
     */
    public boolean isCheckedBeforeIteration() {
        return false;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnDo(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printDo(this);
    }
}
