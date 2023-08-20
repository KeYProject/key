/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.convenience;

import recoder.java.ProgramElement;

/**
 * Walks a syntax tree in iterator-like fashion.
 *
 * @author AL
 */
public abstract class AbstractTreeWalker implements ProgramElementWalker, Cloneable {

    ProgramElement[] stack;

    int count;

    ProgramElement current;

    protected AbstractTreeWalker(int initialStackCapacity) {
        stack = new ProgramElement[initialStackCapacity];
    }

    public AbstractTreeWalker(ProgramElement root) {
        stack = new ProgramElement[16];
        reset(root);
    }

    public AbstractTreeWalker(ProgramElement root, int initialStackCapacity) {
        stack = new ProgramElement[Math.max(8, initialStackCapacity)];
        reset(root);
    }

    /**
     * Reset the walker reusing existing objects.
     */
    protected void reset(ProgramElement root) {
        while (count > 0) {
            stack[--count] = null;
        }
        stack[count++] = current = root;
    }

    /**
     * Proceed to the next occurrance of an object of the given class or a subclass thereof. If
     * there is no such object, the walk is finished.
     */
    public boolean next(Class c) {
        while (next()) {
            if (c.isInstance(current)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Proceed to the next occurrance of an object accepted by the given filter. If there is no such
     * object, the walk is finished.
     */
    public boolean next(ModelElementFilter filter) {
        while (next()) {
            if (filter.accept(current)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Proceeds to the next element, if available. Returns true, if there is one, false otherwise.
     *
     * @return true if the iterator points to an object.
     */
    public abstract boolean next();

    /**
     * Returns the current ProgramElement of the iteration, or null if there is no more element.
     *
     * @return the current ProgramElement, or <CODE>null</CODE>.
     * @see #next()
     */
    public final ProgramElement getProgramElement() {
        return current;
    }

    /**
     * Creates a new walker pointing to the same position as the current one.
     */
    public AbstractTreeWalker clone() {
        try {
            AbstractTreeWalker here = (AbstractTreeWalker) super.clone();
            here.stack = stack.clone();
            return here;
        } catch (CloneNotSupportedException cnse) {
            return null;
        }
    }

    public boolean equals(Object x) {
        if (!(x instanceof AbstractTreeWalker)) {
            return false;
        }
        AbstractTreeWalker atw = (AbstractTreeWalker) x;
        if (atw.current != current) {
            return false;
        }
        if (atw.count != count) {
            return false;
        }
        if (atw.stack == null) {
            return stack == null;
        }
        for (int i = 0; i < count; i += 1) {
            if (atw.stack[i] != stack[i]) {
                return false;
            }
        }
        return true;
    }

    public int hashCode() {
        return System.identityHashCode(current);
    }
}
