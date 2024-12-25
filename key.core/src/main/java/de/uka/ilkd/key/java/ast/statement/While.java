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
 * While.
 */
public class While extends LoopStatement {
    /**
     * create a new While statement with no position info and no comments but guard and body set
     *
     * @param guard an expression.
     * @param body  a statement.
     */
    public While(Expression guard, Statement body) {
        this(null, null, new Guard(guard), body);
    }

    /**
     * While.
     *
     * @param pos   a PositionInformation.
     * @param guard an expression.
     * @param body  a statement.
     */
    public While(@Nullable PositionInfo pos, Expression guard, Statement body) {
        this(pos, null, new Guard(guard), body);
    }

    public While(@Nullable PositionInfo pi, @Nullable List<Comment> c, Guard guard, Statement body) {
        super(pi, c, null, null, guard, body);
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
