/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.pat;

import org.key_project.logic.SyntaxElement;

public class IdentPattern implements Pattern {
    private final SyntaxElement ident;

    public IdentPattern(SyntaxElement ident) {
        this.ident = ident;
    }

    @Override
    public SyntaxElement getChild(int n) {
        if (n == 0) {
            return ident;
        }
        throw new IndexOutOfBoundsException("IdentPattern has only one child");
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public String toString() {
        return ident.toString();
    }
}
