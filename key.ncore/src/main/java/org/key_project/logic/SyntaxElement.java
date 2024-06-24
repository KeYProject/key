/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic;

/**
 * This interface declares the methods common to all logic related (terms, formulas, programs)
 * AST nodes.
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

    default SyntaxElementCursor getCursor() {
        return new SyntaxElementCursor(this);
    }
}
