/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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

    @Override
    public String toString() {
        return ";";
    }

    @Override
    public boolean equals(Object o) {
        if (o == null || getClass() != o.getClass())
            return false;
        return true;
    }

    @Override
    public int hashCode() {
        return 32472243;
    }
}
