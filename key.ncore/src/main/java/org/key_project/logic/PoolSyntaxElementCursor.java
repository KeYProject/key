/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic;

import java.util.ArrayDeque;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * An iterator that walks in first-depth order through the syntax element. It allows to jump to
 * siblings.
 */
public class PoolSyntaxElementCursor {
    private static final int POOL_SIZE = 100;
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
     * currently
     * empty The used cursor have to be explicitly released by the user via
     * {@link #release()}
     *
     * @return a pooled {@link PoolSyntaxElementCursor} or a new one if the {@link #CURSOR_POOL} is
     *         currently
     *         empty
     */
    public static PoolSyntaxElementCursor get(SyntaxElement se) {
        PoolSyntaxElementCursor c = null;
        synchronized (CURSOR_POOL) {
            if (!CURSOR_POOL.isEmpty()) {
                c = CURSOR_POOL.pop();
            }
        }
        if (c != null) {
            c.stack.push(MutablePair.get(se, 0));
        } else {
            c = new PoolSyntaxElementCursor(se);
        }
        return c;
    }

    /**
     * top element on stack contains always the pair whose first component is the element to be
     * returned by {@link #gotoNext()} while the second points to the child to be visited next (or
     * equals the arity of the first component if no such child exists) For all elements on the
     * stack that are not the top element the second component is less than the arity of the syntax
     * element in
     * the first component
     */
    private final ArrayDeque<MutablePair> stack = new ArrayDeque<>();

    private PoolSyntaxElementCursor() {
    }

    private PoolSyntaxElementCursor(SyntaxElement se) {
        stack.push(MutablePair.get(se, 0));
    }

    public boolean hasNext() {
        return !stack.isEmpty();
    }

    public boolean hasNextSibling() {
        return stack.size() > 1;
    }

    public SyntaxElement getCurrentElement() {
        @SuppressWarnings("nullness")
        @NonNull
        SyntaxElement element = stack.peek().first;
        return element;
    }

    private /* @ helper @ */ void gotoNextHelper() {
        if (stack.isEmpty()) {
            return;
        }
        MutablePair el = stack.peek();
        do {
            @SuppressWarnings("nullness")
            final int firstChildCount = el.first.getChildCount();
            if (el.second < firstChildCount) {
                final int oldPos = el.second;
                final SyntaxElement oldSE = el.first;
                if (oldPos + 1 >= firstChildCount) {
                    // we visited all children of that element
                    // so it can be removed from the stack
                    stack.pop().release(); // el's components are set to null
                }
                el.second += 1;
                el = MutablePair.get(oldSE.getChild(oldPos), 0);
                stack.push(el);
            } else {
                stack.pop().release();
            }
        } while (!stack.isEmpty() && (el = stack.peek()).second != 0);
    }

    public void gotoNextSibling() {
        stack.pop().release();
        gotoNextHelper();
    }

    public void release() {
        stack.forEach(MutablePair::release);
        stack.clear();
        if (CURSOR_POOL.size() < POOL_SIZE) {
            synchronized (CURSOR_POOL) {
                CURSOR_POOL.push(this);
            }
        }
    }

    public void gotoNext() {
        gotoNextHelper();
    }

    /**
     * A mutable tuple of two types
     */
    private static class MutablePair {
        private static final int PAIR_POOL_SIZE = 1000;

        /**
         * {@link #CURSOR_POOL} of {@link MutablePair} as these are created very often and
         * short-living we reuse them as far as possible
         * <br>
         * The used cursor have to be explicitly released by the user via {@link #release()}
         */
        private static final ArrayDeque<MutablePair> PAIR_POOL = new ArrayDeque<>();
        static {
            for (int i = 0; i < PAIR_POOL_SIZE; i++) {
                PAIR_POOL.push(new MutablePair(null, 0));
            }
        }

        /**
         * returns a pooled {@link MutablePair} or a new one if the {@link #PAIR_POOL} is currently
         * empty The used MutablePair have to be explicitly released by the user via
         * {@link #release()}
         *
         * @return a pooled {@link MutablePair} or a new one if the {@link #PAIR_POOL} is currently
         *         empty
         */
        static MutablePair get(SyntaxElement first, int second) {
            MutablePair pair = null;
            synchronized (PAIR_POOL) {
                if (!PAIR_POOL.isEmpty()) {
                    pair = PAIR_POOL.pop();
                }
            }
            if (pair != null) {
                pair.set(first, second);
            } else {
                pair = new MutablePair(first, second);
            }
            return pair;
        }


        @Nullable
        SyntaxElement first;
        int second;

        public MutablePair(@Nullable SyntaxElement first, int second) {
            this.first = first;
            this.second = second;
        }

        public final void set(SyntaxElement first, int second) {
            this.first = first;
            this.second = second;
        }

        public final void release() {
            first = null;
            second = 0;
            if (PAIR_POOL.size() < PAIR_POOL_SIZE) {
                synchronized (PAIR_POOL) {
                    PAIR_POOL.push(this);
                }
            }
        }

        @Override
        public String toString() {
            return "MutablePair [first=" + first + ", second=" + second + "]";
        }
    }
}
