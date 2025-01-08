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

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public class LetStatement implements Statement, VariableDeclaration {
    private final Pattern pat;
    private final RustType type;
    private final Expr init;

    private int hashCode = -1;

    public LetStatement(Pattern pat, RustType type, @Nullable Expr init) {
        this.pat = pat;
        this.type = type;
        this.init = init;
    }


    @Override
    public @NonNull SyntaxElement getChild(int n) {
        return switch (n) {
        case 0 -> pat;
        case 1 -> type;
        case 2 -> Objects.requireNonNull(init);
        default -> throw new IndexOutOfBoundsException("LetStatement has three children");
        };
    }

    @Override
    public int getChildCount() {
        return 3;
    }

    public RustType type() {
        return type;
    }

    public Pattern getPattern() {
        return pat;
    }

    @Override
    public String toString() {
        return "let " + pat + ": " + type + " = " + init;
    }

    @Override
    public void visit(Visitor v) {
        throw new RuntimeException("TODO @ DD");
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
