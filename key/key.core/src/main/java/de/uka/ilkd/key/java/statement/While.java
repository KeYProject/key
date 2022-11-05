package de.uka.ilkd.key.java.statement;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.visitor.Visitor;

/**
 * While.
 */

public class While extends LoopStatement {

    /**
     * While.
     */

    public While() {}

    /**
     * While.
     *
     * @param guard an expression.
     * @param body a statement.
     * @param pos a PositionInformation.
     */

    public While(Expression guard, Statement body, PositionInfo pos, ExtList comments) {
        super(guard, body, comments, pos);
    }

    /**
     * create a new While statement with no position info and no comments but guard and body set
     *
     * @param guard an expression.
     * @param body a statement.
     */

    public While(Expression guard, Statement body) {
        super(guard, body, new ExtList());
    }

    /**
     * While.
     *
     * @param guard an expression.
     * @param body a statement.
     * @param pos a PositionInformation.
     */

    public While(Expression guard, Statement body, PositionInfo pos) {
        super(guard, body, pos);
    }

    public SourceElement getLastElement() {
        return (body != null) ? body.getLastElement() : this;
    }

    /**
     * Is checked before iteration.
     *
     * @return the boolean value.
     */

    public boolean isCheckedBeforeIteration() {
        return true;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnWhile(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printWhile(this);
    }
}
