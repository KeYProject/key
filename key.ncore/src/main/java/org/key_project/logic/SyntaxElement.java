/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic;

/**
 * This interface defines the base class for abstract syntax tree structures regardless of the
 * underlying language. All tree-like structures should implement this interface.
 * <p>
 * For navigating the syntax elements, see {@link SyntaxElementCursor}.
 * </p>
 * <p>
 * If a class has no children, it should implement {@link TerminalSyntaxElement}.
 * </p>
 */
public interface SyntaxElement {
    /**
     * Get the {@code n}-th child of this syntax element.
     *
     * @param n index of the child.
     * @return the {@code n}-th child of this syntax element.
     * @throws IndexOutOfBoundsException if there is no {@code n}-th child.
     */
    SyntaxElement getChild(int n);

    /**
     *
     * @return the number of children of this syntax element.
     */
    int getChildCount();

    /**
     * @return a new cursor for the subtree with the current node as root.
     */
    default SyntaxElementCursor getCursor() {
        return new SyntaxElementCursor(this);
    }
}
