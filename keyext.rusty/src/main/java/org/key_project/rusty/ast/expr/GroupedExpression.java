/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;

//spotless:off
public record GroupedExpression(Expr expr) implements Expr {
    @Override
    public void visit(Visitor v) {
        v.performActionOnGroupedExpression(this);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) return expr;
        throw new IndexOutOfBoundsException("GroupedExpression has only one child");
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public String toString() {
        return "(" + expr + ")";
    }

    @Override
    public Type type(Services services) {
        return expr.type(services);
    }
}
//spotless:on