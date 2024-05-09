/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.statement;

import java.util.List;

import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * Do.
 *
 */
public class Do extends LoopStatement {
    /**
     * Do.
     *
     * @param guard
     *        an expression.
     * @param body
     *        a statement.
     */
    public Do(Expression guard, Statement body, ExtList l, PositionInfo pos) {
        super(guard, body, l, pos);
    }

    /**
     * Do.
     *
     * @param guard
     *        an expression.
     * @param body
     *        a statement.
     */
    public Do(Expression guard, Statement body, PositionInfo pos) {
        super(guard, body, pos);
    }

    public Do(PositionInfo pi, List<Comment> c, Guard guard, Statement body) {
        super(pi, c, null, null, guard, body);
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
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnDo(this);
    }
}
