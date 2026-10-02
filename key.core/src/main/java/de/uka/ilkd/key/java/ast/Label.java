/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast;

import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.parsing.Position;

public interface Label extends TerminalProgramElement {

    Comment[] getComments();

    SourceElement getFirstElement();

    SourceElement getLastElement();

    void visit(Visitor v);

    Position getStartPosition();

    Position getEndPosition();

}
