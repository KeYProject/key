/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.ty.RustType;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;

//spotless:off
public record TypeCastExpression(Expr expr, RustType ty) implements Expr {
    @Override
    public void visit(Visitor v) {
        v.performActionOnTypeCastExpression(this);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) {
            return expr;
        }
        if (n == 1) {
            return ty;
        }
        throw new IndexOutOfBoundsException("TypeCastExpression has only 2 children");
    }

    @Override
    public int getChildCount() {
        return 2;
    }

    @Override
    public String toString() {
        return expr + " as " + ty;
    }

    @Override
    public Type type(Services services) {
        return ty.type();
    }
}
//spotless:on