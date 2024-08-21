/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import java.util.Objects;
import java.util.stream.Collectors;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.stmt.Statement;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

public class BlockExpression implements Expr {
    private final ImmutableList<? extends Statement> statements;
    private final Expr value;

    public BlockExpression(ImmutableList<? extends Statement> statements, Expr value) {
        this.statements = statements;
        this.value = value;
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (0 <= n && n < statements.size())
            return Objects.requireNonNull(statements.get(n));
        if (n == statements.size())
            return value;
        throw new IndexOutOfBoundsException("BlockExpression has less than " + n + " children");
    }

    @Override
    public int getChildCount() {
        return statements.size() + 1;
    }

    public ImmutableList<? extends Statement> getStatements() {
        return statements;
    }

    public Expr getValue() {
        return value;
    }

    @Override
    public String toString() {
        return "{\n"
            + statements.stream().map(s -> "\t" + s.toString()).collect(Collectors.joining("\n"))
            + "\n\t" + value.toString()
            + "\n}";
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnBlockExpression(this);
    }
}
