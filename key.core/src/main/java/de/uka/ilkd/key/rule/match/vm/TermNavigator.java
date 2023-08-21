/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import java.util.ArrayDeque;

import de.uka.ilkd.key.logic.Term;

/**
 * An iterator that walks in first-depth order through the term. It allows to jump to siblings.
 */
public class TermNavigator {


    private static final int POOL_SIZE = 100;
    /**
     * TERM_NAVIGATOR_POOL of TermNavigator as these are created very often and short-living we
     * reuse them as far as possible
     *
     * The used TermNavigator have to be explicitly released by the user via {@link #release()}
     */
    private static final ArrayDeque<TermNavigator> TERM_NAVIGATOR_POOL = new ArrayDeque<>();
    static {
        for (int i = 0; i < POOL_SIZE; i++) {
            TERM_NAVIGATOR_POOL.push(new TermNavigator());
        }
    }

    /**
     * returns a pooled {@link TermNavigator} or a new one if the TERM_NAVIGATOR_POOL is currently
     * empty The used TermNavigator have to be explicitly released by the user via
     * {@link #release()}
     *
     * @return a pooled {@link TermNavigator} or a new one if the TERM_NAVIGATOR_POOL is currently
     *         empty
     */
    public static TermNavigator get(Term term) {
        TermNavigator tn = null;
        synchronized (TERM_NAVIGATOR_POOL) {
            if (!TERM_NAVIGATOR_POOL.isEmpty()) {
                tn = TERM_NAVIGATOR_POOL.pop();
            }
        }
        if (tn != null) {
            tn.stack.push(MutablePair.get(term, 0));
        } else {
            tn = new TermNavigator(term);
        }
        return tn;
    }


    /**
     * top element on stack contains always the pair whose first component is the element to be
     * returned by {@link #next()} while the second points to the child to be visited next (or
     * equals the arity of the first component if no such child exists) For all elements on the
     * stack that are not the top element the second component is less than the arity of the term in
     * the first component
     */
    private final ArrayDeque<MutablePair> stack = new ArrayDeque<>();

    private TermNavigator() {
    }

    private TermNavigator(Term term) {
        stack.push(MutablePair.get(term, 0));
    }

    public boolean hasNext() {
        return !stack.isEmpty();
    }

    public boolean hasNextSibling() {
        return stack.size() > 1;
    }


    public Term getCurrentSubterm() {
        return stack.peek().first;
    }

    private /* @ helper @ */ void gotoNextHelper() {
        if (stack.isEmpty()) {
            return;
        }
        do {
            MutablePair el = stack.peek();
            if (el.second < el.first.arity()) {
                final int oldPos = el.second;
                final Term oldTerm = el.first;
                el.second += 1;
                if (el.second >= oldTerm.arity()) {
                    // we visited all children of that term
                    // so it can be removed from the stack
                    stack.pop().release(); // el's components are set to null
                }
                el = MutablePair.get(oldTerm.sub(oldPos), 0);
                stack.push(el);
            } else {
                stack.pop().release();
            }
        } while (!stack.isEmpty() && stack.peek().second != 0);
    }

    public void gotoNext() {
        gotoNextHelper();
    }

    public void gotoNextSibling() {
        stack.pop().release();
        gotoNextHelper();
    }

    public void release() {
        stack.forEach(MutablePair::release);
        stack.clear();
        if (TERM_NAVIGATOR_POOL.size() < POOL_SIZE) {
            synchronized (TERM_NAVIGATOR_POOL) {
                TERM_NAVIGATOR_POOL.push(this);
            }
        }
    }


    /**
     * A mutable tuple of two types
     */
    private static class MutablePair {

        private static final int PAIR_POOL_SIZE = 1000;

        /**
         * TERM_NAVIGATOR_POOL of TermNavigator.MutablePair as these are created very often and
         * short-living we reuse them as far as possible
         *
         * The used TermNavigator have to be explicitly released by the user via {@link #release()}
         */
        private static final ArrayDeque<MutablePair> PAIR_POOL = new ArrayDeque<>();
        static {
            for (int i = 0; i < PAIR_POOL_SIZE; i++) {
                PAIR_POOL.push(new MutablePair(null, null));
            }
        }

        /**
         * returns a pooled {@link MutablePair} or a new one if the TERM_NAVIGATOR_POOL is currently
         * empty The used MutablePair have to be explicitly released by the user via
         * {@link #release()}
         *
         * @return a pooled {@link MutablePair} or a new one if the TERM_NAVIGATOR_POOL is currently
         *         empty
         */
        static MutablePair get(Term first, Integer second) {
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


        Term first;
        Integer second;

        public MutablePair(Term first, Integer second) {
            this.first = first;
            this.second = second;
        }

        public final void set(Term first, Integer second) {
            this.first = first;
            this.second = second;
        }

        public final void release() {
            first = null;
            second = null;
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
