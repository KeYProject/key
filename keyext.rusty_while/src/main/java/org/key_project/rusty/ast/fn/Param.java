/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.fn;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.pat.Pattern;
import org.key_project.rusty.ast.ty.Type;

public class Param implements RustyProgramElement {
    private final Pattern pattern;
    private final Type type;

    public Param(Pattern pattern, Type type) {
        this.pattern = pattern;
        this.type = type;
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public SyntaxElement getChild(int n) {
        if (n == 0) {
            return pattern;
        }
        throw new IndexOutOfBoundsException("Param has only one child");
    }

    @Override
    public String toString() {
        return pattern.toString() + ": " + type.toString();
    }
}
