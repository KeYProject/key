/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.ast;

import org.key_project.logic.SyntaxElement;

public class AssignmentExpression implements Expr {
    private final Expr lhs;
    private final Expr rhs;

    public AssignmentExpression(Expr lhs, Expr rhs) {
        this.lhs = lhs;
        this.rhs = rhs;
    }


    @Override
    public SyntaxElement getChild(int n) {
        return switch (n) {
        case 0 -> lhs;
        case 1 -> rhs;
        default -> throw new IndexOutOfBoundsException(
            "AssignmentExpression has only two children");
        };
    }

    @Override
    public int getChildCount() {
        return 2;
    }

    @Override
    public String toString() {
        return lhs + " = " + rhs;
    }
}
