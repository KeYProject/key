/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.compiler;

import org.key_project.logic.SyntaxElement;

import org.jspecify.annotations.Nullable;

/**
 * A positional cursor over the children of one syntax element, used when matching a program whose
 * pattern may consume a <em>variable</em> number of source children (a list schema variable). It
 * keeps the parent {@code element} and the index {@code childPos} of the child to be matched next.
 * For convenience, the index {@code -1} means the element itself is the one to be matched — used
 * when a match starts at an element rather than inside one (e.g. an empty block).
 *
 * <p>
 * The cursor navigates purely through {@link SyntaxElement#getChild} /
 * {@link SyntaxElement#getChildCount}, so it works for any language's program elements.
 */
public final class ProgramChildCursor {

    /** the parent element whose children are matched ({@code childPos == -1}: matched itself) */
    private final SyntaxElement element;
    private int childPos;

    public ProgramChildCursor(SyntaxElement element, int childPos) {
        this.element = element;
        this.childPos = childPos;
    }

    /**
     * @return the element the cursor points at: the parent itself for index {@code -1}, its
     *         {@code childPos}-th child for a valid index, or {@code null} when the children are
     *         exhausted
     */
    public @Nullable SyntaxElement getSource() {
        if (childPos == -1) {
            return element;
        }
        if (childPos < element.getChildCount()) {
            return element.getChild(childPos);
        }
        return null;
    }

    /** advances the cursor by one position (from {@code -1} to the first child) */
    public void next() {
        childPos++;
    }

    public int getChildPos() {
        return childPos;
    }

    public void setChildPos(int childPos) {
        this.childPos = childPos;
    }

    public SyntaxElement getElement() {
        return element;
    }
}
