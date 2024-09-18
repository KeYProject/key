/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.pat.Pattern;
import org.key_project.rusty.ast.ty.RustType;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public record ClosureParam(@NonNull Pattern pattern, @Nullable RustType ty) implements SyntaxElement {
    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) {return pattern;}
        if (n == 1 && ty != null) {return ty;}
        throw new IndexOutOfBoundsException("ClosureParam has only 2 children");
    }

    @Override
    public int getChildCount() {
        return 2;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(pattern);
        if (ty != null) {sb.append(": ").append(ty);}
        return sb.toString();
    }
}
