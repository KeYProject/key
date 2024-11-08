/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.pat.Pattern;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

//spotless:off
public record MatchArm(Pattern pattern, @Nullable Expr guard, Expr body) implements RustyProgramElement {
    @Override
    public void visit(Visitor v) {
        v.performActionOnMatchArm(this);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) {
            return pattern;
        }
        if (guard != null) {
            if (n == 1) {
                return guard;
            }
            --n;
        }
        if (n == 1) {
            return body;
        }
        throw new IndexOutOfBoundsException("MatchArm has only " + getChildCount() + " children");
    }

    @Override
    public int getChildCount() {
        return 2 + (guard == null ? 0 : 1);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(pattern);
        if (guard != null) {
            sb.append(" if ").append(guard);
        }
        sb.append(" => ").append(body);
        return "";
    }
}
//spotless:on