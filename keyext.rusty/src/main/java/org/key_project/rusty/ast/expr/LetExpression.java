/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.pat.Pattern;
import org.key_project.rusty.ast.ty.RustType;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

// spotless:off
public record LetExpression(Pattern pat, @Nullable RustType ty, Expr init, Type type) implements Expr {
    @Override
    public void visit(Visitor v) {
        v.performActionOnLetExpression(this);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) return pat;
        --n;
        if(n == 0 && ty != null) return ty;
        if(ty != null) --n;
        if (n==0) return init;
        throw new IndexOutOfBoundsException("LetExpression only has "+  getChildCount() + " children");
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
}
//spotless:on
