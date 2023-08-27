/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * While.
 */

public class While extends LoopStatement {

    /**
     * While.
     */

    public While() {}

    /**
     * While.
     *
     * @param guard an expression.
     * @param body a statement.
     * @param pos a PositionInformation.
     */

    public While(Expression guard, Statement body, PositionInfo pos, ExtList comments) {
        super(guard, body, comments, pos);
    }

    /**
     * create a new While statement with no position info and no comments but guard and body set
     *
     * @param guard an expression.
     * @param body a statement.
     */

    public While(Expression guard, Statement body) {
        super(guard, body, new ExtList());
    }

    /**
     * While.
     *
     * @param guard an expression.
     * @param body a statement.
     * @param pos a PositionInformation.
     */

    public While(Expression guard, Statement body, PositionInfo pos) {
        super(guard, body, pos);
    }

    public SourceElement getLastElement() {
        return (body != null) ? body.getLastElement() : this;
    }

    /**
     * Is checked before iteration.
     *
     * @return the boolean value.
     */

    public boolean isCheckedBeforeIteration() {
        return true;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnWhile(this);
    }
}
