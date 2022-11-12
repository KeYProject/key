/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
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
