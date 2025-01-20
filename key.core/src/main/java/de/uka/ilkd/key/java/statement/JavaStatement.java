/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.Statement;

import org.key_project.util.ExtList;

/**
 * Default implementation for non-terminal Java statements.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class JavaStatement extends JavaNonTerminalProgramElement implements Statement {


    /**
     * Java statement.
     */
    public JavaStatement() {
    }

    /**
     * Java statement.
     *
     * @param children the children of this AST element as KeY classes. May contain: Comments
     */
    public JavaStatement(ExtList children) {
        super(children);
    }

    public JavaStatement(ExtList children, PositionInfo pos) {
        super(children, pos);
    }

    public JavaStatement(PositionInfo pos) {
        super(pos);
    }

}
