/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;

public record UnitStructExpression(PathExpression path) implements Expr {
    @Override
    public void visit(Visitor v) {
        v.performActionOnUnitStructExpression(this);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if(n == 0) return path;
        throw new IndexOutOfBoundsException("UnitStructExpression has only 1 child");
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public String toString() {
        return path.toString();
    }
}
