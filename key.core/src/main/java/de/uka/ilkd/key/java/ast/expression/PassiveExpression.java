/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.jspecify.annotations.Nullable;

import java.util.List;

/**
 * Marks an active statement as inactive.
 */
public class PassiveExpression extends ParenthesizedExpression {
    public PassiveExpression(Expression child) {
        super(null, null, child);
    }

    public PassiveExpression(@Nullable PositionInfo pi, @Nullable List<Comment> c, Expression accept) {
        super(pi, c, accept);
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnPassiveExpression(this);
    }
}
