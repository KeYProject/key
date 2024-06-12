/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.ast;

import java.util.stream.Collectors;

import org.key_project.logic.SyntaxElement;
import org.key_project.util.collection.ImmutableList;

public class BlockExpression implements Expr {
    private final ImmutableList<? extends Statement> statements;

    public BlockExpression(ImmutableList<? extends Statement> statements) {
        this.statements = statements;
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
        return "{" + statements.stream().map(Statement::toString).collect(Collectors.joining("; "))
            + "}";
    }
}
