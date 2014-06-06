// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util.pp;

/**
 * The backend for a {@link Layouter}.  An object satisfying this
 * interface can act as a receiver for the layed out text produced by
 * a {@link Layouter}.  A <code>Backend</code> must also provide the
 * maximum line width available through the {@link #lineWidth()}
 * method.  Finally, it is responsible for calculating (with {@link
 * #measure(String)} the amount of space it actually needs to print a
 * given string.  For instance, if strings printed through a {@link
 * Layouter} are actually known to be in HTML, {@link
 * #measure(String)} can return the size of the text, not including
 * markup.
 *
 * <P>There is currently no provision to handle proportional fonts,
 * and there might never be.
 *
 * @author Martin Giese
 * @see Layouter
 *
 */

public interface Backend {
    /** Append a String <code>s</code> to the output.  <code>s</code> 
     * contains no newlines. */
    void print(String s) throws java.io.IOException;

    /** Start a new line. */
    void newLine() throws java.io.IOException;

    /** Closes this backend */
    void close() throws java.io.IOException;

    /** Flushes any buffered output */
    void flush() throws java.io.IOException;

    /** Gets called to record a <code>mark()</code> call in the input. */
    void mark(Object o);

    /** Returns the available space per line */
    int lineWidth();

    /** Returns the space required to print the String <code>s</code> */
    int measure(String s);

}