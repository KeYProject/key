/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.statement;

import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.visitor.Visitor;

import java.util.List;

/**
 * Empty statement.
 *
 * @author <TT>AutoDoc</TT>
 */
public class EmptyStatement extends JavaProgramElement
        implements Statement, TerminalProgramElement {

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY. May contain: Comments
     */
    public EmptyStatement() {
        super();
    }

    public EmptyStatement(PositionInfo pi, List<Comment> c) {
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
