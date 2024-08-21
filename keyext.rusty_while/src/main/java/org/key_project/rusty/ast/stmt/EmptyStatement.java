package org.key_project.rusty.ast.stmt;

import org.key_project.logic.TerminalSyntaxElement;
import org.key_project.rusty.ast.visitor.Visitor;

/**
 * Empty statement.
 */
public class EmptyStatement implements Statement, TerminalSyntaxElement {
    /**
     * Constructor for the transformation of COMPOST ASTs to KeY. May contain: Comments
     */
    public EmptyStatement() {
        super();
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnEmptyStatement(this);
    }
}
