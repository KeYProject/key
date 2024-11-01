/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import java.util.Objects;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.abstraction.TupleType;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NonNull;

//spotless:off
public record TupleExpression(ImmutableArray<Expr> elements) implements Expr {
    public static TupleExpression UNIT = new TupleExpression(new ImmutableArray<>());

    public boolean isUnit() {
        return this == UNIT;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnTupleExpression(this);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        return Objects.requireNonNull(elements.get(n));
    }

    @Override
    public int getChildCount() {
        return elements().size();
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("(");
        for (int i = 0; i < elements().size(); i++) {
            if (i > 0) {
                sb.append(", ");
            }
            sb.append(elements().get(i));
        }
        return sb.append(")").toString();
    }

    @Override
    public Type type(Services services) {
        if (isUnit()) {
            return TupleType.UNIT;
        }
        throw new UnsupportedOperationException();
    }
}
//spotless:on