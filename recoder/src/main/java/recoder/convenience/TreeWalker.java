/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.convenience;

import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;

/**
 * Walks a syntax tree in depth-first order. This roughly yields the syntactical order of the
 * program elements, except for closing parentheses and other implicit lexical tokens.
 *
 * @author AL
 */
public class TreeWalker extends AbstractTreeWalker {

    protected TreeWalker(int initialStackCapacity) {
        super(initialStackCapacity);
    }

    public TreeWalker(ProgramElement root) {
        super(root);
    }

    public TreeWalker(ProgramElement root, int initialStackCapacity) {
        super(root, initialStackCapacity);
    }

    /**
     * Reset the walker to a new start position reusing existing objects.
     */
    public void reset(ProgramElement root) {
        super.reset(root);
    }

    public boolean next() {
        if (count == 0) {
            current = null;
            return false;
        }
        current = stack[--count]; // pop
        if (current instanceof NonTerminalProgramElement) {
            NonTerminalProgramElement nt = (NonTerminalProgramElement) current;
            int s = nt.getChildCount();
            if (count + s >= stack.length) {
                ProgramElement[] newStack =
                    new ProgramElement[Math.max(stack.length * 2, count + s)];
                System.arraycopy(stack, 0, newStack, 0, count);
                stack = newStack;
            }
            for (int i = s - 1; i >= 0; i -= 1) {
                stack[count++] = nt.getChildAt(i); // push
            }
        }
        return true;
    }

}
