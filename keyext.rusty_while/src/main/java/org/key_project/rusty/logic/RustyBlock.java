/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import org.key_project.logic.Program;
import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.RustyProgramElement;

public class RustyBlock implements Program {
    private final RustyProgramElement program;

    public RustyBlock(RustyProgramElement program) {
        this.program = program;
    }

    public RustyProgramElement program() { return program; }

    @Override
    public SyntaxElement getChild(int n) {
        if (n == 0)
            return program;
        throw new IndexOutOfBoundsException("RustyBlock " + this + " has only one child");
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    public boolean isEmpty() {
        return false;
    }

    @Override
    public String toString() {
        return program.toString();
    }
}
