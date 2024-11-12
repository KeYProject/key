/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import java.util.Objects;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.abstraction.TupleType;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.pat.Pattern;
import org.key_project.rusty.ast.ty.RustType;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.util.ExtList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public final class LetExpression implements Expr {
    private final Pattern pat;
    private final @Nullable RustType ty;
    private final Expr init;

    public LetExpression(Pattern pat, @Nullable RustType ty, Expr init) {
        this.pat = pat;
        this.ty = ty;
        this.init = init;
    }

    public LetExpression(ExtList children) {
        pat = children.removeFirstOccurrence(Pattern.class);
        ty = children.removeFirstOccurrence(RustType.class);
        init = children.removeFirstOccurrence(Expr.class);
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnLetExpression(this);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0)
            return pat;
        --n;
        if (n == 0 && ty != null)
            return ty;
        if (ty != null)
            --n;
        if (n == 0)
            return init;
        throw new IndexOutOfBoundsException(
            "LetExpression only has " + getChildCount() + " children");
    }

    @Override
    public int getChildCount() {
        return 2 + (ty == null ? 0 : 1);
    }

    @Override
    public String toString() {
        var sb = new StringBuilder();
        sb.append("let ");
        sb.append(pat);
        if (ty != null) {
            sb.append(": ").append(ty);
        }
        sb.append(" = ").append(init).append(" ");
        return sb.toString();
    }

    public Pattern pat() {
        return pat;
    }

    public @Nullable RustType ty() {
        return ty;
    }

    public Expr init() {
        return init;
    }

    @Override
    public Type type(Services services) {
        // Type doesn't relly matter
        return TupleType.UNIT;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == this)
            return true;
        if (obj == null || obj.getClass() != this.getClass())
            return false;
        var that = (LetExpression) obj;
        return Objects.equals(this.pat, that.pat) &&
                Objects.equals(this.ty, that.ty) &&
                Objects.equals(this.init, that.init);
    }

    @Override
    public int hashCode() {
        return Objects.hash(pat, ty, init);
    }

}
