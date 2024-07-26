/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.fn;

import java.util.Objects;
import java.util.stream.Collectors;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.Item;
import org.key_project.rusty.ast.expr.BlockExpression;
import org.key_project.rusty.ast.ty.Type;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

public record Function(Name name, ImmutableList<Param> params, Type returnType,
                       BlockExpression body) implements Item, Named {

    @Override
    public int getChildCount() {
        return 3 + params.size();
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (0 <= n && n < params.size())
            return Objects.requireNonNull(params.get(n));
        n -= params.size();
        if (n == 0)
            return body;
        throw new IndexOutOfBoundsException("No child at index " + n);
    }

    @Override
    public String toString() {
        return "fn " + name() + "("
                + params.map(Param::toString).stream().collect(Collectors.joining(", ")) + ") -> "
                + returnType + " " + body;
    }
}
