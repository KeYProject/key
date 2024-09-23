/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.rusty.ldt.BoolLDT;

import org.jspecify.annotations.NonNull;

public class BooleanLiteralExpression extends LiteralExpression {
    private final boolean value;

    public BooleanLiteralExpression(boolean value) {
        this.value = value;
    }


    @Override
    public @NonNull SyntaxElement getChild(int n) {
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

    @Override
    public boolean equals(Object obj) {
        if (obj == null || obj.getClass() != this.getClass()) {
            return false;
        }
        return value == (((BooleanLiteralExpression) obj).value);
    }

    @Override
    public Name getLDTName() {
        return BoolLDT.NAME;
    }

    public boolean getValue() {
        return value;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnBooleanLiteralExpression(this);
    }
}
