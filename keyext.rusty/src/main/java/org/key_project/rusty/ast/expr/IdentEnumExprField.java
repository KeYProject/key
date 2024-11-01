/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.Identifier;

import org.jspecify.annotations.NonNull;

//spotless:off
public record IdentEnumExprField(Identifier ident, Expr expr) implements EnumExprField {
    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) return ident;
        if (n == 1) return expr;
        throw new IndexOutOfBoundsException("IdentEnumExprField has only 2 children");
    }

    @Override
    public int getChildCount() {
        return 2;
    }

    @Override
    public String toString() {
        return ident + ": " + expr;
    }
}
//spotless:on