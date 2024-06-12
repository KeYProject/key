/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.ast;

import org.key_project.logic.SyntaxElement;

public class LetStatement implements Statement {
    private final Pattern pat;
    private final Type type;
    private final Expr init;

    public LetStatement(Pattern pat, Type type, Expr init) {
        this.pat = pat;
        this.type = type;
        this.init = init;
    }


    @Override
    public SyntaxElement getChild(int n) {
        return switch (n) {
        case 0 -> pat;
        case 1 -> type;
        case 2 -> init;
        default -> throw new IndexOutOfBoundsException("LetStatement has three children");
        };
    }

    @Override
    public int getChildCount() {
        return 3;
    }

    @Override
    public String toString() {
        return "let " + pat + ": " + type + " = " + init;
    }
}
