/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic;

import java.util.ArrayDeque;
import java.util.Arrays;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * An iterator that walks in first-depth order through the syntax element. It allows to jump to
 * siblings.
 *
 * <p>
 * The traversal stack is kept in two plain arrays (element, index of the next child to
 * visit) owned by the cursor, so advancing the cursor neither allocates nor synchronizes.
 * This matters: the cursor is the innermost loop of taclet matching.
 */
public class PoolSyntaxElementCursor {
    private static final int POOL_SIZE = 100;
    private static final int INITIAL_STACK_SIZE = 64;

    /**
     * A pool of {@link PoolSyntaxElementCursor} as these are created very often and short-living we
     * reuse them as far as possible
     * <br>
     * The used PoolSyntaxElementCursor have to be explicitly released by the user via
     * {@link #release()}
     */
    private static final ArrayDeque<PoolSyntaxElementCursor> CURSOR_POOL = new ArrayDeque<>();
    static {
        for (int i = 0; i < POOL_SIZE; i++) {
            CURSOR_POOL.push(new PoolSyntaxElementCursor());
        }
    }

    /**
     * returns a pooled {@link PoolSyntaxElementCursor} or a new one if the {@link #CURSOR_POOL} is
     * currently empty. The used cursor has to be explicitly released by the user via
     * {@link #release()}
     *
     * @return a pooled {@link PoolSyntaxElementCursor} or a new one if the {@link #CURSOR_POOL} is
     *         currently empty
     */
    public static PoolSyntaxElementCursor get(SyntaxElement se) {
        PoolSyntaxElementCursor c = null;
        synchronized (CURSOR_POOL) {
            if (!CURSOR_POOL.isEmpty()) {
                c = CURSOR_POOL.pop();
            }
        }
        if (c == null) {
            c = new PoolSyntaxElementCursor();
        }
        c.push(se);
        return c;
    }

    /**
     * The traversal stack: {@code elements[0..top]} are the syntax elements on the path
     * from the root to the current element; {@code nextChild[i]} is the index of the child
     * of {@code elements[i]} to be visited next. The top entry is the element returned by
     * {@link #getCurrentElement()}; for all entries below the top, {@code nextChild} is
     * less than the arity of the corresponding element.
     */
    private @Nullable SyntaxElement[] elements = new SyntaxElement[INITIAL_STACK_SIZE];
    private int[] nextChild = new int[INITIAL_STACK_SIZE];
    private int top = -1;

    private PoolSyntaxElementCursor() {
    }

    private void push(SyntaxElement se) {
        if (++top == elements.length) {
            elements = Arrays.copyOf(elements, 2 * elements.length);
            nextChild = Arrays.copyOf(nextChild, 2 * nextChild.length);
        }
        elements[top] = se;
        nextChild[top] = 0;
    }

    private void pop() {
        elements[top] = null;
        top--;
    }

    public boolean hasNext() {
        return top >= 0;
    }

    public boolean hasNextSibling() {
        return top >= 1;
    }

    @SuppressWarnings("nullness")
    public @NonNull SyntaxElement getCurrentElement() {
        // cannot be null as then hasNext would have returned false (and top would be -1)
        final SyntaxElement current = elements[top];
        assert current != null;
        return current;
    }

    private /* @ helper @ */ void gotoNextHelper() {
        if (top < 0) {
            return;
        }
        do {
            final SyntaxElement se = elements[top];
            final int pos = nextChild[top];
            assert se != null;
            @SuppressWarnings("nullness") // se cannot be null, if elements[top] is null then we
                                          // iterated over the whole term and top is < 0
            final int childCount = se.getChildCount();
            if (pos < childCount) {
                if (pos + 1 >= childCount) {
                    // we visited all children of that element,
                    // so it can be removed from the stack
                    pop();
                } else {
                    nextChild[top] = pos + 1;
                }
                push(se.getChild(pos));
            } else {
                pop();
            }
        } while (top >= 0 && nextChild[top] != 0);
    }

    public void gotoNextSibling() {
        pop();
        gotoNextHelper();
    }

    public void gotoNext() {
        gotoNextHelper();
    }

    public void release() {
        while (top >= 0) {
            elements[top] = null;
            top--;
        }
        synchronized (CURSOR_POOL) {
            if (CURSOR_POOL.size() < POOL_SIZE) {
                CURSOR_POOL.push(this);
            }
        }
    }
}
