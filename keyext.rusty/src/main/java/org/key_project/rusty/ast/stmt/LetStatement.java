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
import org.key_project.util.ExtList;

public class LetStatement implements Statement, VariableDeclaration {
    private final Pattern pat;
    private final RustType type;
    private final Expr init;

    public LetStatement(Pattern pat, RustType type, @Nullable Expr init) {
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
        if (n == 0) {return pat;}
        if (n == 1) {return type;}
        if (n == 2 && init != null) {return init;}
        throw new IndexOutOfBoundsException("LetStatement has " + getChildCount() + " children");
    }

    @Override
    public int getChildCount() {
        return init == null ? 2 : 3;
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
        return "let " + pat + ": " + type + " = " + init;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnLetStatement(this);
    }
}
