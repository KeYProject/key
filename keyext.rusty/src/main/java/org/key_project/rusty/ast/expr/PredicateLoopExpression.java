/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.Label;
import org.key_project.rusty.ast.abstraction.TupleType;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

// spotless:off
public record PredicateLoopExpression(@Nullable Label label, Expr pred,
                                      BlockExpression body) implements LoopExpression {
    @Override
    public void visit(Visitor v) {

    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0 && label != null) {
            return label;
        }
        if (label != null) --n;
        if (n == 0) return pred;
        if (n == 1) return body;
        throw new IndexOutOfBoundsException("Predicate loop expression has only 2 children");
    }

    @Override
    public int getChildCount() {
        return 2;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        if (label != null) sb.append(label).append(": ");
        sb.append("while ").append(pred).append(' ').append(body);
        return sb.toString();
    }

    @Override
    public Type type(Services services) {
        return TupleType.UNIT;
    }
}
//spotless:on
