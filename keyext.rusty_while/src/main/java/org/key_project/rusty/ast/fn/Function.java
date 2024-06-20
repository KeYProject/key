/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.fn;

import java.util.stream.Collectors;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.Item;
import org.key_project.rusty.ast.expr.BlockExpression;
import org.key_project.rusty.ast.ty.Type;
import org.key_project.util.collection.ImmutableList;

public class Function implements Item, Named {
    private final Name name;
    private final ImmutableList<Param> params;
    private final Type returnType;
    private final BlockExpression body;

    public Function(Name name, ImmutableList<Param> params, Type returnType, BlockExpression body) {
        this.name = name;
        this.params = params;
        this.returnType = returnType;
        this.body = body;
    }

    public ImmutableList<Param> getParams() {
        return params;
    }

    @Override
    public Name name() {
        return name;
    }

    public Type getReturnType() {
        return returnType;
    }

    public BlockExpression getBody() {
        return body;
    }

    @Override
    public int getChildCount() {
        return 3 + params.size();
    }

    @Override
    public SyntaxElement getChild(int n) {
        if (0 <= n && n < params.size())
            return params.get(n);
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
