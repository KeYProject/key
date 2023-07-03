/**
 * represents a java label
 */
package de.uka.ilkd.key.java.ast;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.visitor.Visitor;

public interface Label extends TerminalProgramElement {

    Comment[] getComments();

    SourceElement getFirstElement();

    SourceElement getLastElement();

    void visit(Visitor v);

    Position getStartPosition();

    Position getEndPosition();

}
