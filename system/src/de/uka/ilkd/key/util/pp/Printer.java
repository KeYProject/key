// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.util.pp;

import java.io.IOException;
import java.util.ArrayList;

/** The intermediate layer of the pretty printing library.  Using the
 * block size information provided by the {@link Layouter} class, this
 * decides where to insert line breaks.  It tries to break as few
 * blocks as possible.  */

class Printer {

    /** Mask for break type flags.  These flags are logically or-ed
     * onto the margins in the marginStack to remember what happens
     * with the block in question. */
    private static final int BREAK_MASK   = 0x70000000;
    /** Flag to indicate this block fits into the current line */
    private static final int FITS         = 0x00000000;
    /** Flag to indicate this block will be broken consistently */
    private static final int CONSISTENT   = 0x10000000;
    /** Flag to indicate this block will be broken inconsistently */
    private static final int INCONSISTENT = 0x20000000;

    /** total line length available */
    private final int lineWidth;
    
    /** position in current line. */
    private int pos;

    /** total chars written */
    private int totalOut=0;

    /** Back-end for the pretty-printed output */
    private Backend back;

    /** stack to remember value of <code>pos</code> in nested blocks */
    private ArrayList marginStack = new ArrayList(10);


    /** Create a printer.  It will write its output to <code>writer</code>.
     * Lines have a maximum width of <code>lineWidth</code>. */
    Printer(Backend back) {
	this.back = back;
	lineWidth = back.lineWidth();
	pos = 0;
    }


    /** write the String <code>s</code> to <code>out</code> */
    void print(String s) throws IOException {
	back.print(s);
	pos+=back.measure(s);
	totalOut+=back.measure(s);
    }

    /** begin a block */
    void openBlock(boolean consistent,int indent,
		   int followingLength) {
	if (followingLength + pos > lineWidth) {
	    push(pos+indent,consistent?CONSISTENT:INCONSISTENT);
	} else {
	    push(0,FITS);
	}
    }

    /** end a block */
    void closeBlock() {
	pop();
    }

    /**
     * write a break.  <code>followingLength</code> should be the
     * space needed by the material up to the next corresponding
     * closeBlock() or printBreak(), and is used to decide whether the
     * current line is continues, or a new (indented) line is begun.
     * */
    void printBreak(int width,int offset, int followingLength) 
	throws IOException {

	if (topBreak()==CONSISTENT || 
	    (topBreak()==INCONSISTENT 
	     && followingLength > (lineWidth-pos)) ) {
	    
	    pos = topMargin() + offset;

	    newLine();
	} else {
	    writeSpaces(width);
	    pos+=width;
	}
    }

    void mark(Object o) {
	back.mark(o);
    }

    void indent(int width, int offset) 
	throws IOException
    {
	int newMargin = topMargin()+offset;
	if (topBreak() != FITS) {
	    if(newMargin > pos) {
		writeSpaces(newMargin-pos);
		pos=newMargin;
	    }
	} else {
	    writeSpaces(width);
	    pos+=width;
	}
    }

    /** Close the output stream. */
    void close() throws IOException {
	back.close();
    }

    /** Flush the output stream. */
    void flush() throws IOException {
	back.flush();
    }

    /** Return the amount of space currently left on this line. */
    int space() {
	return lineWidth-pos;
    }

    /** Return the line width of this Printer. */
    int lineWidth() {
	return lineWidth;
    }

    private void push(int n,int breaks) {
	marginStack.add(Integer.valueOf(n|breaks));
    }

    /** Pop one element from the space stack. */
    private void pop() {
	try {
	    marginStack.remove(marginStack.size()-1);
	} catch (IndexOutOfBoundsException e) {
	    throw new UnbalancedBlocksException();
	}
    }

    /** return the topmost element of the space stack without popping it. */
    private int top() {
	try {
	    return ((Integer)marginStack.get(marginStack.size()-1)).intValue();
	} catch (IndexOutOfBoundsException e) {
	    throw new UnbalancedBlocksException();
	}
    }

    private int topMargin() {
	return top() & ~BREAK_MASK;
    }

    private int topBreak() {
	return top() & BREAK_MASK;
    }

    /** Start a new line and indent according to <code>pos</code>
     */
    private void newLine() throws IOException {
	back.newLine();
	totalOut++;
	if (pos>0) {
	    writeSpaces(pos);
	}
    }

    /** how many spaces */
    private static final int SPACES = 128;

    /** a String containing <code>SPACES</code> spaces */
    private static final String spaces;

    /* initialize spaces */
    static {
	StringBuffer sb = new StringBuffer(SPACES);
	for(int i=0;i<SPACES;i++) {
	    sb.append(' ');
	}
	spaces = sb.toString();	
    }

    private void writeSpaces(int n) throws IOException {
	while (n>SPACES) {
	    back.print(spaces);
	    n-=SPACES;
	}
	back.print(spaces.substring(0,n));
	totalOut+=n;
    }
}
