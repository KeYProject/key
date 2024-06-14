/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;

public class BooleanLiteralExpression extends LiteralExpression {
    private final boolean value;

    public BooleanLiteralExpression(boolean value) {
        this.value = value;
    }


    @Override
    public SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException("BooleanLiteralExpression has no children");
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public String toString() {
        return "" + value;
    }
}
