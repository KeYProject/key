/**
 * represents a java label
 */
package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.visitor.Visitor;

public interface Label extends TerminalProgramElement {

    Comment[] getComments();

    SourceElement getFirstElement();

    SourceElement getLastElement();

    void prettyPrint(PrettyPrinter w) throws java.io.IOException;

    void visit(Visitor v);

    Position getStartPosition();

    Position getEndPosition();

    Position getRelativePosition();

}
