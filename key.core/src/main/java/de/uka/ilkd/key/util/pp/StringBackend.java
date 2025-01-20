/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.pp;

/**
 * A {@link Backend} which appends all output to a StringBuffer. The {@link #mark(Object o)} method
 * does nothing in this implementation. There is a method {@link #count()} which returns the number
 * of characters written by this so far. The method {@link #toString()} gets the output written so
 * far.
 */
public class StringBackend<M> {
    protected final StringBuilder out;

    /**
     * Create a new StringBackend. This will accumulate output in a fresh, private StringBuffer.
     */
    public StringBackend() {
        this.out = new StringBuilder();
    }

    /**
     * Append a String <code>s</code> to the output. <code>s</code> contains no newlines.
     */
    public void print(String s) {
        out.append(s);
    }

    /** Start a new line. */
    public void newLine() {
        out.append('\n');
    }

    /** Gets called to record a <code>mark()</code> call in the input. */
    public void mark(M o) {}

    /** Returns the number of characters written through this backend. */
    public int count() {
        return out.length();
    }

    /** Returns the accumulated output */
    public String result() {
        return out.toString();
    }
}
