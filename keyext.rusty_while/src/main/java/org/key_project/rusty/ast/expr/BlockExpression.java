/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import java.util.stream.Collectors;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.stmt.Statement;
import org.key_project.util.collection.ImmutableList;

public class BlockExpression implements Expr {
    private final ImmutableList<? extends Statement> statements;
    private final Expr value;

    public BlockExpression(ImmutableList<? extends Statement> statements, Expr value) {
        this.statements = statements;
        this.value = value;
    }

    @Override
    public SyntaxElement getChild(int n) {
        return statements.get(n);
    }

    @Override
    public int getChildCount() {
        return statements.size();
    }

    @Override
    public String toString() {
        return "{\n"
            + statements.stream().map(s -> "\t" + s.toString()).collect(Collectors.joining("\n"))
            + "\n\t" + value.toString()
            + "\n}";
    }
}
