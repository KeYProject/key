/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.pat;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.logic.op.sv.OperatorSV;

import org.jspecify.annotations.NonNull;

public record SchemaVarPattern(boolean reference, boolean mut, OperatorSV operatorSV) implements Pattern {
    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) return operatorSV;
        throw new IndexOutOfBoundsException("SchemaVarPattern has only one child");
    }

    @Override
    public int getChildCount() {
        return 1;
    }
}
