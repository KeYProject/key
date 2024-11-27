/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import java.util.Objects;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.ty.FnDefType;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.rusty.logic.op.ProgramFunction;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NonNull;

public class CallExpression implements Call {
    private final Expr callee;
    private final ImmutableArray<Expr> params;

    public CallExpression(Expr callee, ImmutableArray<Expr> params) {
        this.callee = callee;
        this.params = params;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnCallExpression(this);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) {
            return callee;
        }
        --n;
        return Objects.requireNonNull(params.get(n));
    }

    @Override
    public int getChildCount() {
        return 1 + params.size();
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(callee);
        sb.append("(");
        for (int i = 0; i < params.size(); i++) {
            if (i > 0) {
                sb.append(", ");
            }
            sb.append(params.get(i));
        }
        sb.append(")");
        return sb.toString();
    }

    @Override
    public Type type(Services services) {
        var fnTy = (FnDefType) callee.type(services);
        return fnTy.fn().returnType().type();
    }

    @Override
    public ProgramFunction function(Services services) {
        var fnTy = (FnDefType) callee.type(services);
        return services.getRustInfo().getFunction(fnTy.fn());
    }

    public Expr callee() {
        return callee;
    }

    public ImmutableArray<Expr> params() {
        return params;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == this)
            return true;
        if (obj == null || obj.getClass() != this.getClass())
            return false;
        var that = (CallExpression) obj;
        return Objects.equals(this.callee, that.callee) &&
                Objects.equals(this.params, that.params);
    }

    @Override
    public int hashCode() {
        return Objects.hash(callee, params);
    }
}
