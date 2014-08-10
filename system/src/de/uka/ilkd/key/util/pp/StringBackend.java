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

/** A {@link Backend} which appends all output to a StringBuffer.
 * The {@link #mark(Object o)} method does nothing in this
 * implementation.  There is a method {@link #count()} which returns
 * the number of characters written by this so far.  
 * The method {@link #getString()} gets the output written so far.
 */
public class StringBackend implements Backend {
    protected StringBuffer out;
    protected int initOutLength;
    protected int lineWidth;
    
    /** Create a new StringBackend.  This will append all output to
     * the given StringBuffer <code>sb</code>.    */
    public StringBackend(StringBuffer sb,int lineWidth) {
	this.lineWidth = lineWidth;
	this.out = sb;
	this.initOutLength = sb.length();
    }

    /** Create a new StringBackend.  This will accumulate output in
     * a fresh, private StringBuffer. */
    public StringBackend(int lineWidth) {
	this(new StringBuffer(lineWidth),lineWidth);
    }

    /** Append a String <code>s</code> to the output.  <code>s</code> 
     * contains no newlines. */
    public void print(String s) throws java.io.IOException {
	out.append(s);
    }

    /** Start a new line. */
    public void newLine() throws java.io.IOException {
	out.append('\n');
    }

    /** Closes this backend */
    public void close() throws java.io.IOException {
	return;
    }

    /** Flushes any buffered output */
    public void flush() throws java.io.IOException {
	return;
    }

    /** Gets called to record a <code>mark()</code> call in the input. */
    public void mark(Object o) {
	return;
    }

    /** Returns the number of characters written through this backend.*/
    public int count() {
	return out.length()-initOutLength;
    }

    /** Returns the available space per line */
    public int lineWidth() {
	return lineWidth;
    }

    /** Returns the space required to print the String <code>s</code> */
    public int measure(String s) {
	return s.length();
    }

    /** Returns the accumulated output */
    public String getString() {
	return out.toString();
    }
}