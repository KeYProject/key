/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.pat.Pattern;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public record IfLetExpression(Pattern pattern, Expr expr, ThenBranch then, @Nullable Expr elseExpr) implements Expr {
    @Override
    public void visit(Visitor v) {
        v.performActionOnIfLetExpression(this);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) {return pattern;}
        if (n == 1) {return expr;}
        if (n == 2) {return then;}
        if (n == 3 && elseExpr != null) {return elseExpr;}
        throw new IndexOutOfBoundsException("IfLetExpression  has less than " + n + " children");
    }

    @Override
    public int getChildCount() {
        return 3 + (elseExpr == null ? 0 : 1);
    }


    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("if let ").append(pattern).append(" = ").append(expr).append(" ").append(then);
        if (elseExpr != null) sb.append(" else ").append(elseExpr);
        return sb.toString();
    }


    @Override
    public Type type(Services services) {
        return then.type(services);
    }
}
