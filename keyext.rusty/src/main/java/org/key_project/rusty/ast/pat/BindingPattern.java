/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.pat;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.rusty.logic.op.ProgramVariable;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

// spotless:off
public record BindingPattern(boolean ref, boolean mutRef, boolean mut, ProgramVariable pv,
                             @Nullable Pattern opt) implements Pattern {

public     BindingPattern {
       assert pv != null : "BindingPattern cannot have a null variable";
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnBindingPattern(this);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) return pv;
        if (n == 1 && opt != null) {
            return opt;
        }
        throw new IndexOutOfBoundsException("BindingPattern has only " + getChildCount() + " children");
    }

    @Override
    public int getChildCount() {
        return opt == null ? 1 : 2;
    }

    @Override
    public String toString() {
        var sb = new StringBuilder();
        if (mut) sb.append("mut ");
        sb.append(pv);
        if (opt != null) sb.append(" @ ").append(opt);
        return sb.toString();
    }
}
//spotless:on
