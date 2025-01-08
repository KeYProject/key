/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.stmt;


import java.util.Objects;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.VariableDeclaration;
import org.key_project.rusty.ast.expr.Expr;
import org.key_project.rusty.ast.pat.Pattern;
import org.key_project.rusty.ast.ty.RustType;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.util.ExtList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public class LetStatement implements Statement, VariableDeclaration {
    private final Pattern pat;
    private final RustType type;
    private final Expr init;

    private int hashCode = -1;

    public LetStatement(Pattern pat, @Nullable RustType type, @Nullable Expr init) {
        this.pat = pat;
        this.type = type;
        this.init = init;
    }

    public LetStatement(ExtList changeList) {
        pat = changeList.removeFirstOccurrence(Pattern.class);
        type = changeList.removeFirstOccurrence(RustType.class);
        init = changeList.removeFirstOccurrence(Expr.class);
    }


    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) {
            return pat;
        }
        --n;
        if (n == 0 && type != null) {
            return type;
        }
        if (type != null)
            --n;
        if (n == 0 && init != null) {
            return init;
        }
        throw new IndexOutOfBoundsException("LetStatement has " + getChildCount() + " children");
    }

    @Override
    public int getChildCount() {
        int res = 1;
        if (type != null) {
            res += 1;
        }
        if (init != null) {
            res += 1;
        }
        return res;
    }

    public RustType type() {
        return type;
    }

    public Pattern getPattern() {
        return pat;
    }

    public boolean hasInit() {
        return init != null;
    }

    public Expr getInit() {
        return init;
    }

    @Override
    public String toString() {
        var sb = new StringBuilder();
        sb.append("let ").append(pat);
        if (type != null) {
            sb.append(": ").append(type);
        }
        if (hasInit()) {
            sb.append(" = ").append(init);
        }
        return sb.append(';').toString();
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnLetStatement(this);
    }

    @Override
    public int hashCode() {
        if (hashCode == -1) {
            return hashCode;
        }
        final int hash = computeHashCode();
        this.hashCode = hash;
        return hash;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null || getClass() != obj.getClass())
            return false;
        final LetStatement that = (LetStatement) obj;
        return pat.equals(that.pat) && Objects.equals(type, that.type)
                && Objects.equals(init, that.init);
    }
}
