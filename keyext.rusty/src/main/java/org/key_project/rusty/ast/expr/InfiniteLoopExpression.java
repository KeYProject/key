/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import java.util.Objects;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.Label;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.util.ExtList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public final class InfiniteLoopExpression implements LoopExpression, LabeledExpression {
    private final @Nullable Label label;
    private final Expr body;

    public InfiniteLoopExpression(@Nullable Label label, Expr body) {
        this.label = label;
        this.body = body;
    }

    public InfiniteLoopExpression(ExtList list) {
        label = list.get(Label.class);
        body = list.get(Expr.class);
    }

    public @Nullable Label label() {
        return label;
    }

    public @NonNull Expr body() {
        return body;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnInfiniteLoop(this);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0 && label != null)
            return label;
        if (n == 0)
            return body;
        throw new IndexOutOfBoundsException("Infinite loop expression has only 1 child");
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        if (label != null)
            sb.append(label).append(": ");
        sb.append("loop ").append(body);
        return sb.toString();
    }

    @Override
    public Type type(Services services) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean equals(Object o) {
        if (o == null || getClass() != o.getClass())
            return false;
        InfiniteLoopExpression that = (InfiniteLoopExpression) o;
        return Objects.equals(label, that.label) && Objects.equals(body, that.body);
    }

    @Override
    public int hashCode() {
        return Objects.hash(label, body);
    }
}
