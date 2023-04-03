package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * Break.
 *
 */

public class Break extends LabelJumpStatement {

    /**
     * Break.
     */

    public Break() {
        super();
    }

    /**
     * Break.
     *
     * @param label a name for the label.
     */
    public Break(Label label) {
        super(label);
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes. May contain: Comments, a
     *        ProgramElementName (as label of the label jump statement)
     */
    public Break(ExtList children) {
        super(children);
        // label=(ProgramElementName)children.get(ProgramElementName.class);
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnBreak(this);
    }
}
