/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.fn;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.pat.Pattern;
import org.key_project.rusty.ast.ty.RustType;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;

public record FunctionParamPattern(Pattern pattern, RustType type) implements FunctionParam {
    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) {
            return pattern;
        }
        if (n == 1) {
            return type;
        }
        throw new IndexOutOfBoundsException("Param has only 2 children");
    }

    @Override
    public String toString() {
        return pattern.toString() + ": " + type.toString();
    }

    @Override
    public void visit(Visitor v) {
        throw new RuntimeException("Shouldn't be called");
    }
}
