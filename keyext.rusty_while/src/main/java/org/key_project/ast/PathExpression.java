/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.ast;

import org.key_project.logic.SyntaxElement;

public class PathExpression implements Expr {
    private final SyntaxElement var;

    public PathExpression(SyntaxElement var) {
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
