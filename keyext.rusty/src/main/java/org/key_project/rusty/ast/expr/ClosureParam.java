/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.pat.Pattern;
import org.key_project.rusty.ast.ty.Type;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public record ClosureParam(@NonNull Pattern pattern, @Nullable Type ty) implements SyntaxElement {
    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) {return pattern;}
        throw new IndexOutOfBoundsException("ClosureParam has only 1 child");
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(pattern);
        if (ty != null) {sb.append(": ").append(ty);}
        return sb.toString();
    }
}
