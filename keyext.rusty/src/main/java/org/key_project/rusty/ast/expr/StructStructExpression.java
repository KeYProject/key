/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import java.util.Objects;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.PathInExpression;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NonNull;

// spotless:off
public record StructStructExpression(PathInExpression path, ImmutableArray<StructExprField> fields,
                                     boolean withRest) implements Expr {
    @Override
    public void visit(Visitor v) {
        v.performActionOnFieldStructExpression(this);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) {
            return path;
        }
        return Objects.requireNonNull(fields.get(n - 1));
    }

    @Override
    public int getChildCount() {
        return 1 + fields.size();
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(path).append(" {\n");
        for (int i = 0; i < fields.size(); i++) {
            if (i > 0) {
                sb.append(",\n");
            }
            sb.append('\t').append(fields.get(i));
            if (i == fields.size() - 1 && withRest) {
                sb.append("\t..");
            }
        }
        sb.append('}');
        return sb.toString();
    }

    @Override
    public Type type(Services services) {
        throw new UnsupportedOperationException();
    }
}
//spotless:on
