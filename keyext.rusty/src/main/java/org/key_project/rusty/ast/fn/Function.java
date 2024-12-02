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
import org.key_project.rusty.ast.ty.RustType;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NonNull;

public final class Function implements Item, Named {
    private final Name name;
    private final ImplicitSelfKind selfKind;
    private ImmutableArray<FunctionParam> params;
    private final RustType returnType;
    private BlockExpression body;

    public Function(Name name, ImplicitSelfKind selfKind, ImmutableArray<FunctionParam> params,
            RustType returnType, BlockExpression body) {
        this.name = name;
        this.selfKind = selfKind;
        this.params = params;
        this.returnType = returnType;
        this.body = body;
    }

    public enum ImplicitSelfKind {
        Imm,
        Mut,
        RefImm,
        RefMut,
        None,
    }

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
            return returnType;
        if (n == 1)
            return body;
        throw new IndexOutOfBoundsException("No child at index " + n);
    }

    @Override
    public String toString() {
        return "fn " + name() + "("
            + params.stream().map(Object::toString).collect(Collectors.joining(", ")) + ") -> "
            + returnType + " " + body;
    }

    @Override
    public void visit(Visitor v) {
        throw new RuntimeException("TODO @ DD");
    }

    @Override
    public @NonNull Name name() {
        return name;
    }

    public ImplicitSelfKind selfKind() {
        return selfKind;
    }

    public ImmutableArray<FunctionParam> params() {
        return params;
    }

    public FunctionParam getParam(int i) {
        return params.get(i);
    }

    public void setParams(ImmutableArray<FunctionParam> params) {
        this.params = params;
    }

    public RustType returnType() {
        return returnType;
    }

    public BlockExpression body() {
        return body;
    }

    public void setBody(BlockExpression body) {
        this.body = body;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == this)
            return true;
        if (obj == null || obj.getClass() != this.getClass())
            return false;
        var that = (Function) obj;
        return Objects.equals(this.name, that.name) &&
                Objects.equals(this.selfKind, that.selfKind) &&
                Objects.equals(this.params, that.params) &&
                Objects.equals(this.returnType, that.returnType) &&
                Objects.equals(this.body, that.body);
    }

    @Override
    public int hashCode() {
        return Objects.hash(name, selfKind, params, returnType, body);
    }

}
