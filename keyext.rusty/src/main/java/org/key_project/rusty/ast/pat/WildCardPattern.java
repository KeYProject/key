/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.pat;

import org.key_project.logic.SyntaxElement;

import org.jspecify.annotations.NonNull;
import org.key_project.rusty.ast.expr.Expr;
import org.key_project.rusty.ast.visitor.Visitor;

public class WildCardPattern implements Pattern {
    public static WildCardPattern WILDCARD = new WildCardPattern();

    private WildCardPattern() {}


    @Override
    public @NonNull SyntaxElement getChild(int n) {
        throw new IllegalArgumentException("WildCardPattern has no child");
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnWildCardPattern(this);
    }
}
