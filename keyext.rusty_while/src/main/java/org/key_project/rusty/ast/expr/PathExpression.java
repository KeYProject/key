/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.Identifier;

public class PathExpression implements Expr {
    private final Identifier var;

    public PathExpression(Identifier var) {
        this.var = var;
    }


    @Override
    public SyntaxElement getChild(int n) {
        if (n == 0) {
            return var;
        }
        throw new IndexOutOfBoundsException("PathExpression has only one child");
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public String toString() {
        return var.toString();
    }
}
