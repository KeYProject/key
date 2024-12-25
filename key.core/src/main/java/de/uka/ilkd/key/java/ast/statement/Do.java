/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.statement;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.SourceElement;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.jspecify.annotations.Nullable;

import java.util.List;

/**
 * Do.
 */
public class Do extends LoopStatement {
    /**
     * Do.
     *
     * @param guard an expression.
     * @param body  a statement.
     */
    public Do(Expression guard, Statement body, PositionInfo pos) {
        super(guard, body, pos);
    }

    public Do(@Nullable PositionInfo pi, @Nullable List<Comment> c, Guard guard, Statement body) {
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
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnDo(this);
    }
}
