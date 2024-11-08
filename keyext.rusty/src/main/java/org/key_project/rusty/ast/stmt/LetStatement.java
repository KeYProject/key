/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.stmt;


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
    public boolean equals(Object obj) {
        if (obj == this) {
            return true;
        }
        if (obj == null || obj.getClass() != this.getClass()) {
            return false;
        }
        final var other = (LetStatement) obj;
        if (init == null && other.init != null || init != null && !init.equals(other.init)) {
            return false;
        }
        return pat.equals(other.pat) && type.equals(other.type);
    }

    @Override
    public int hashCode() {
        int hashcode = 5;
        hashcode = 31 * hashcode + pat.hashCode();
        hashcode = 31 * hashcode + type.hashCode();
        hashcode = 31 * hashcode + (init == null ? 0 : init.hashCode());
        return hashcode;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnLetStatement(this);
    }
}
