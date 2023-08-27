/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * Do.
 *
 */
public class Do extends LoopStatement {

    /**
     * Do.
     */
    public Do() {
        super();
    }

    /**
     * Do.
     *
     * @param guard an expression.
     */
    public Do(Expression guard) {
        super(guard);
    }

    /**
     * Do.
     *
     * @param guard an expression.
     * @param body a statement.
     */
    public Do(Expression guard, Statement body, ExtList l, PositionInfo pos) {
        super(guard, body, l, pos);
    }

    /**
     * Do.
     *
     * @param guard an expression.
     * @param body a statement.
     */
    public Do(Expression guard, Statement body, PositionInfo pos) {
        super(guard, body, pos);
    }

    public SourceElement getLastElement() {
        return this;
    }

    /**
     * Is checked before iteration.
     *
     * @return the boolean value.
     */
    public boolean isCheckedBeforeIteration() {
        return false;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnDo(this);
    }
}
