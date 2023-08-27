/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.pp;

/**
 * The backend for a {@link Layouter}. An object satisfying this interface can act as a receiver for
 * the layed out text produced by a {@link Layouter}. A <code>Backend</code> must also provide the
 * maximum line width available through the {@link #lineWidth()} method.
 *
 * <P>
 * There is currently no provision to handle proportional fonts, and there might never be.
 *
 * @author Martin Giese
 * @see Layouter
 *
 */

public interface Backend<M> {
    /**
     * Append a String <code>s</code> to the output. <code>s</code> contains no newlines.
     */
    void print(String s);

    /** Start a new line. */
    void newLine();

    /** Closes this backend */
    void close();

    /** Flushes any buffered output */
    void flush();

    /** Gets called to record a <code>mark()</code> call in the input. */
    void mark(M o);

    /** Returns the available space per line */
    int lineWidth();
}
