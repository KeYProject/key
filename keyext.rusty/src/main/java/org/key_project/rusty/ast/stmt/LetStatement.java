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
        throw new RuntimeException("TODO @ DD");
    }
}
