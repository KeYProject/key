package de.uka.ilkd.key.java.statement;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.TerminalProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;



/**
 * Empty statement.
 *
 * @author <TT>AutoDoc</TT>
 */
public class EmptyStatement extends JavaProgramElement
        implements Statement, TerminalProgramElement {

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes.
     */
    public EmptyStatement(ExtList children) {
        super(children);
    }

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

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printEmptyStatement(this);
    }

}
