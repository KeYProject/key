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

import java.io.IOException;
import java.util.List;
import java.util.StringTokenizer;

/**
 * This class pretty-prints information using line breaks and
 * indentation.  For instance, it can be used to print
 * <pre>
 *   while (i>0) {
 *     i--;
 *     j++;
 *   }
 * </pre>
 * instead of 
 * <pre>
 *   while (i>0) { i
 *   --; j++;}
 * </pre>
 * if a maximum line width of 15 characters is chosen.
 *
 * <P>The formatted output is directed to a <em>backend</em> which
 * might write it to an I/O stream, append it to the text of a GUI
 * componenet or store it in a string.  The {@link Backend} interface
 * encapsulates the concept of backend.  Apart from handling the
 * output, the backend is also asked for the available line width and
 * for the amount of space needed to print a string.  This makes it
 * possible to include e.g. HTML markup in the output which does not
 * take up any space.  There are two convenience implementations
 * {@link WriterBackend} and {@link StringBackend}, which write the
 * output to a {@link java.io.Writer}, resp. a 
 *
 * {@link java.lang.String}.
 *
 * <P>The layouter internally keeps track of a current <em>indentation
 * level</em>.  Think of nicely indented Java source code.  Then the
 * indentation level at any point is the number of blank columns to be
 * inserted at the begining of the next line if you inserted a line
 * break.  To increase the indentation level of parts of the text, the
 * input to the layouter is separated into <em>blocks</em>.  The
 * indentation level changes when a block is begun, and it is reset to
 * its previous value when a block is ended.  Of course, blocks maybe
 * nested.
 *
 * <P>In order to break text among several lines, the layouter needs
 * to be told where line breaks are allowed.  A <em>break</em> is a
 * position in the text where there is either a line break (with
 * appropriate indentation) or a number of spaces, if enough material
 * fits in one line.  In order to handle the indentation level
 * properly, breaks should only occur inside blocks.  There are in
 * fact two kinds of blocks: <em>consistent</em> and
 * <em>inconsistent</em> ones.  In a consistent block, line are broken
 * either at all or at none of the breaks.  In an inconsistent block,
 * as much material as possible is put on one line before it is
 * broken.
 *
 * <P>Consider the program above.  It should be printed either as
 * <pre>
 *   while (i>0) { i--; j++; }
 * </pre>
 * or, if there is not enough space on the line, as
 * <pre>
 *   while (i>0) {
 *     i--;
 *     j++;
 *   }
 * </pre>
 * Given a Layouter object <code>l</code>, we could say:
 * <pre>
 * l.begin(true,2).print("while (i>0) {").brk(1,0)
 *  .print("i--;").brk(1,0)
 *  .print("j++;").brk(1,-2)
 *  .print("{").end();
 * </pre>
 *
 * The call to {@link #begin(boolean,int)} starts a consistent block,
 * increasing the indentation level by 2.  The {@link #print(String)}
 * methods gives some actual text to be output.  The call to {@link
 * #brk(int,int)} inserts a break.  The first argument means that one
 * space should be printed at this position if the line is
 * <em>not</em> broken.  The second argument is an offset to be added
 * to the indentation level for the next line, if the line <em>is</em>
 * broken.  The effect of this parameter can be seen in the call
 * <code>brk(1,-2)</code>.  The offset of <code>-2</code> outdents the
 * last line by 2 positions, which aligns the closing brace with the
 * <code>with</code>.
 *
 * <p>If the lines in a block are broken, one sometimes wants to insert
 * spaces up to the current indentation level at a certain position
 * without allowing a line break there.  This can be done using the
 * {@link #ind(int,int)} method.  For instance, one wants to output either
 * <pre>
 *   ...[Good and Bad and Ugly]...
 * </pre>
 * or
 * <pre>
 *   ...[    Good
 *       and Bad
 *       and Ugly]...
 * </pre>
 *
 * Note the four spaces required before <code>Good</code>.  We do this
 * by opening a block which sets the indentation level to the column where the <code>G</code> ends up and outdenting the lines with the <code>and</code>:
 * <pre>
 *   l.print("...[").begin(true,4).ind(0,0).print("Good").brk(1,-4)
 *    .print("and ").print("Bad").brk(1,-4)
 *    .print("and ").print("Ugly").end().print("]...");
 * </pre>
 *
 * Again, the first argument to {@link #ind(int,int)} is a number of
 * spaces to print if the block we are in is printed on one line.  The
 * second argument is an offset to be added to the current indentation
 * level to determine the column to which we should skip.
 *
 * <p>When all text has been sent to a Layouter and all blocks have been
 * ended, the {@link #close()} method should be closed.  This sends
 * all pending output to the backend and invokes the {@link
 * Backend#close()} method, which usually closes I/O streams, etc.
 *
 * <p>Some applications need to keep track of where certain parts of the
 * input text end up in the output.  For this purpose, the Layouter
 * class provides the {@link #mark(Object)} method.  
 *
 * <P>The public methods of this class may be divided into two
 * categories: A small number of <em>primitive</em> methods, as
 * described above, and a host of <em>convenience</em> methods which
 * simplify calling the primitive ones for often-used arguments.  For
 * instance a call to {@link #beginC()} is shorthand for
 * <code>begin(true,ind)</code>, where <code>ind</code> is the default
 * indentation selected when the Layouter was constructed.
 *
 * <P>Most of the methods can throw an {@link UnbalancedBlocksException},
 * which indicates that the sequence of method calls was illegal, i.e.
 * more blocks were ended than begun, the Layouter is closed before all
 * blocks are ended, a break occurs outside of any block, etc.
 *
 * <P>Also, most methods can throw an {@link java.io.IOException}.
 * This only happens if a called method in the backend throws an
 * IOException, in which case that exception is passed through to the
 * caller of the Layouter method.  
 *
 * @author Martin Giese
 * @see Backend
 * */



/*
 * Implementation note: The name of this class is actually a lie.
 * What this class does is calculate the space needed by blocks and
 * portions of blocks between breaks if they are to printed in a
 * single line.  The actual laying out, that is choosing whether to
 * break line or not is done by a Printer object, which in turn sends
 * its output to the Backend.
 *
 */

public class Layouter {

    /** The backend */
    private Backend back;

    /** The Printer used for output. */
    private Printer out;

    /** The list of scanned tokens not yet output. */
    private List<StreamToken> stream = new java.util.LinkedList<StreamToken>();

    /** A stack of <code>OpenBlockToken</code>s and
     * <code>BreakToken</code>s in <code>stream</code>, waiting for
     * their size to be determined.*/
    private List<StreamToken> delimStack = new java.util.LinkedList<StreamToken>();

    /*
     * Some Invariants:
     *
     * delimStack.isEmpty() implies stream.isEmpty()
     *
     * Any OpenBlockToken in stream is also on the demlimStack.
     * The latest BreakToken of any open block in the stream is 
     * also on the delim stack.
     *
     */
    
    
    /** Total size of received strings and blanks, if they were
     * printed in one line.  The difference of this between two states
     * says how much space would be needed to print the intervening
     * stuff without line breaks. */
    private int totalSize=0;

    /** Total size of strings and blanks sent to the Printer <code>out</code>.
     * Subtract this from <code>totalOutput</code> and you get the space
     * needed to print what is still buffered in <code>stream</code> */
    private int totalOutput=0;

    /** The size assigned to things which are guaranteed not to fit on a
     * line.  For good measure, this is intitialized to twice the line
     * width by the constructors. */
    private int largeSize;

    /** A default indentation value used for blocks. */
    private int defaultInd;

    
    // PRIMITIVE CONSTRUCTOR -------------------------------------------

    /**
     * Construts a newly allocated Layouter which will send output to
     * the given {@link Backend} and has the given default indentation.
     *
     * @param back the Backend
     * @param indentation the default indentation
     *
     */

    public Layouter(Backend back,int indentation) {
	this.back = back;
	out = new Printer(back);
	largeSize = 2*back.lineWidth();
	this.defaultInd = indentation;
    }

    // CONVENIENCE CONSTRUCTORS ----------------------------------------

    /** = 80 : The line width for some of the convenience constructors.*/
    public static final int DEFAULT_LINE_WIDTH = 80;

    /** = 2 : The default indentation for some of the convenience 
	constructors */
    public static final int DEFAULT_INDENTATION = 2;


    /** Convenience constructor for a Layouter with a {@link WriterBackend}.
     * The line width is taken to be {@link #DEFAULT_LINE_WIDTH}, and the
     * default indentation {@link #DEFAULT_INDENTATION}. 
     *
     * @param writer the {@link java.io.Writer} the Backend is going to use
     */
    public Layouter(java.io.Writer writer) {
	this(writer,DEFAULT_LINE_WIDTH);
    }

    /** Convenience constructor for a Layouter with a {@link WriterBackend}.
     * The default indentation is taken from {@link #DEFAULT_INDENTATION}. 
     *
     * @param writer the {@link java.io.Writer} the Backend is going to use
     * @param lineWidth the maximum lineWidth the Backend is going to use
     */
    public Layouter(java.io.Writer writer,int lineWidth) {
	this(writer,lineWidth,DEFAULT_INDENTATION);
    }
    
    /** Convenience constructor for a Layouter with a {@link WriterBackend}.
     *
     * @param writer the {@link java.io.Writer} the Backend is going to use
     * @param lineWidth the maximum lineWidth the Backend is going to use
     * @param indentation the default indentation
     */
    public Layouter(java.io.Writer writer,int lineWidth,int indentation) {
	this(new WriterBackend(writer,lineWidth),indentation);
    }

    // PRIMITIVE STREAM OPERATIONS ------------------------------------

    /** Output text material.  The string <code>s</code> should not
     * contain newline characters.  If you have a string with newline
     * characters, and want to retain its formatting, consider using
     * the {@link #pre(String s)} method.  The Layouter will not
     * insert any line breaks in such a string.
     *
     * @param s the String to print.
     * @return this
     */
    public Layouter print(String s) 
    	throws IOException
    {
	if (delimStack.isEmpty()) {
	    out.print(s);
	    totalSize+=back.measure(s);
	    totalOutput+=back.measure(s);
	} else {
	    enqueue(new StringToken(s));
	    totalSize+=back.measure(s);

	    while(totalSize-totalOutput > out.space() &&
		  !delimStack.isEmpty()) {
		popBottom().setInfiniteSize();
		advanceLeft();
	    }
	}
	return this;
    }

    /** Begin a block.  If <code>consistent</code> is set, breaks
     * are either all broken or all not broken.  The indentation
     * level is increased by <code>indent</code>.
     *
     * @param consistent <code>true</code> for consistent block
     * @param indent increment to indentation level
     * @return this
     */
    public Layouter begin(boolean consistent,int indent) {
	StreamToken t = new OpenBlockToken(consistent,indent);
	enqueue(t);
	push(t);
	return this;
    }
    
    /** Ends the innermost block.
     * @return this
     **/
    public Layouter end() 
	throws IOException
    {
	if (delimStack.isEmpty()) {
	    /* then stream is also empty, so output */
	    out.closeBlock();
	} else {
	    enqueue(new CloseBlockToken());
	    
	    StreamToken topDelim = pop();
	    topDelim.setEnd();
	    if (topDelim instanceof BreakToken &&
		!delimStack.isEmpty() ) {
		/* This must be the matching OpenBlockToken */
		StreamToken topOpen = pop();
		topOpen.setEnd();
	    }
	    
	    if ( delimStack.isEmpty() ) {
		/* preserve invariant */
		advanceLeft();
	    }
	}
	return this;
    }

    /**
     * Print a break. This will print <code>width</code> spaces if the
     * line is <em>not</em> broken at this point.  If it <em>is</em>
     * broken, indentation is added to the current indentation level,
     * plus the value of <code>offset</code>.
     *
     * @param width  space to insert if not broken
     * @param offset offset relative to current indentation level
     * @return this
     */
    public Layouter brk(int width,int offset) 
	throws IOException
    {
	if ( !delimStack.isEmpty() ) {
	    StreamToken s = top();
	    if (s instanceof BreakToken) {
		pop();
		s.setEnd();
	    }
	}
	
	StreamToken t = new BreakToken(width,offset);
	enqueue(t);
	push(t);
	totalSize+=width;
	return this;
    }

    /**
     * Indent to a current indentation level if surrounding block is
     * broken.  If the surrounding block fits on one line, insert
     * <code>width</code> spaces.  Otherwise, indent to the current
     * indentation level, plus <code>offset</code>, unless that
     * position has already been exceeded on the current line.  If
     * that is the case, nothing is printed.  No line break is
     * possible at this point.
     *
     * @param width  space to insert if not broken
     * @param offset offset relative to current indentation level
     * @return this
     */
    public Layouter ind(int width, int offset) 
	throws IOException
    {
	if (delimStack.isEmpty()) {
	    out.indent(width,offset);
	    totalSize+=width;
	    totalOutput+=width;
	} else {
	    enqueue(new IndentationToken(width,offset));
	    totalSize+=width;
	}
	return this;
    }

    /**
     * This leads to a call of the {@link Backend#mark(Object)} method
     * of the backend, when the material preceding the call to
     * <code>mark</code> has been printed to the backend, including
     * any inserted line breaks and indentation.  The {@link Object}
     * argument to <code>mark</code> is passed through unchanged to
     * the backend and may be used by the application to pass
     * information about the purpose of the mark.
     *
     * @param o an object to be passed through to the backend.
     * @returns this
     *
     */
    public Layouter mark(Object o) {
	if (delimStack.isEmpty()) {
	    out.mark(o);
	} else {
	    enqueue(new MarkToken(o));
	}
	    return this;
    }

    /**
     * Output any information currently kept in buffers.  This is
     * essentially passed on to the backend.  Note that material in
     * blocks begun but not ended cannot be forced to the output by
     * this method.  Finish all blocks and call <code>flush</code> or
     * {@link #close()} then.
     *
     * @return this
     */
    public Layouter flush() throws IOException {
	out.flush();
	return this;
    }

    /**
     * Close the Layouter.  No more methods should be called after
     * this.  All blocks begun must have been ended by this point.
     * Any pending material is written to the backend, before the
     * {@link Backend#close()} method of the backend is called, which
     * closes any open I/O streams, etc.
     *
     */
    public void close() throws IOException {
	if (!delimStack.isEmpty()) {
	    throw new UnbalancedBlocksException();
	} else {
	    advanceLeft();
	}
	out.close();
    }


    // CONVENIENCE STREAM OPERATIONS ---------------------------------

    /** Begin an inconsistent block.  Add this Layouter's default
     * indentation to the indentation level. 
     * @return this
     */
    public Layouter beginI() {
	return begin(false,defaultInd);
    }

    /** Begin a consistent block.  Add this Layouter's default
     * indentation to the indentation level. 
     * @return this
     */
    public Layouter beginC() {
	return begin(true,defaultInd);
    }

    /** Begin an inconsistent block.  Add <code>indent</code>
     * to the indentation level. 
     * @param indent the indentation for this block
     * @return this
     */
    public Layouter beginI(int indent) {
	return begin(false,indent);
    }

    /** Begin a consistent block.  Add <code>indent</code>
     * to the indentation level. 
     * @param indent the indentation for this block
     * @return this
     */
    public Layouter beginC(int indent) {
	return begin(true,indent);
    }

    /** Begin a block with default indentation.  Add this Layouter's
     * default indentation to the indentation level.  
     * @param consistent <code>true</code> for consistent block
     * @return this */
    public Layouter begin(boolean consistent) {
	return begin(consistent,defaultInd);
    }


    /** Print a break with zero offset. 
     * @param width  space to insert if not broken
     * @return this */
    public Layouter brk(int width) 
	throws IOException
    {
	return brk(width,0);
    }

    /** Print a break with zero offset and width one. 
     * @return this */
    public Layouter brk() 
	throws IOException
    {
	return brk(1);
    }

    /** Print a break with zero offset and large width.  As the large
     * number of spaces will never fit into one line, this amounts to
     * a forced line break. 
     * @return this */
    public Layouter nl() 
	throws IOException
    {
	return brk(largeSize);
    }

    /** Indent with zero offset and zero width.  Just indents
     * to the current indentation level if the block is broken, and
     * prints nothing otherwise.
     * @return this */
    public Layouter ind()
	throws IOException
    {
	return this.ind(0,0);
    }


    /** Layout prefromated text.  This amounts to a (consistent) block
     * with indentation 0, where each line of <code>s</code>
     * (separated by \n) gets printed as a string and newlines become
     * forced breaks.  
     * @param s the pre-formatted string
     * @return this
     */
    public Layouter pre(String s)
	throws IOException
    {
	StringTokenizer st = new StringTokenizer(s,"\n",true);
	beginC(0);
	while(st.hasMoreTokens()) {
	    String line = st.nextToken();
	    if ("\n".equals(line)) {
		nl();
	    } else {
		print(line);
	    }
	}
	end();
	
	return this;
    }


    // PRIVATE METHODS -----------------------------------------------

    /* Delimiter Stack handling */


    /** Push an OpenBlockToken or BreakToken onto the delimStack */
    private void push(StreamToken t) {
	delimStack.add(t);
    }

    /** Pop the topmost Token from the delimStack */
    private StreamToken pop()  {
	try {
	    return (delimStack.remove(delimStack.size()-1));
	} catch (IndexOutOfBoundsException e) {
	    throw new UnbalancedBlocksException();
	}
    }

    /** Remove and return the token from the <em>bottom</em> of the
     * delimStack */
    private StreamToken popBottom()  {
	try {
	    return (delimStack.remove(0));
	} catch (IndexOutOfBoundsException e) {
	    throw new UnbalancedBlocksException();
	}
    }

    /** Return the top of the delimStack, without popping it. */
    private StreamToken top()  {
	try {
	    return delimStack.get(delimStack.size()-1);
	} catch (IndexOutOfBoundsException e) {
	    throw new UnbalancedBlocksException();
	}
    }


    /* stream handling */

    /** Put a StreamToken into the stream (at the end). */
    private void enqueue(StreamToken t) {
	stream.add(t);
    }
    
    /** Get the front token from the stream. */
    private StreamToken dequeue() {
	return (stream.remove(0));
    }

    /** Send tokens from <code>stream<code> to <code>out</code> as long
     * as there are tokens left and their size is known. */
    private void advanceLeft() 
	throws IOException
    {
	StreamToken t;
	while (! stream.isEmpty() &&
	       ((t=stream.get(0)).followingSizeKnown())) {
	    t.print();
	    stream.remove(0);
	    totalOutput+=t.size();
	}
    }

    // STREAM TOKEN CLASSES -----------------------------------------

    /** A stream token.
     */
    private abstract class StreamToken {
	/** Send this token to the Printer {@link #out}. */
	abstract void print() 
	    throws IOException;

	/** Return the size of this token if the block is not broken. */
	abstract int size();
	
	/** Return the `section' size.  For an OpenBlockToken, this is the
	 * size of the whole block, if it is not broken.  For a BreakToken,
	 * it is the size of the material up to the next corresponding
	 * BreakToken or CloseBlockToken.  Otherwise it is the same as
	 * size().  This might only be known after several more tokens 
	 * have been read.  If the value is guaranteed to be larger than
	 * what fits on a line, some large value might be returned instead
	 * of the precise size.
	 */
	int followingSize() {
	    return size();
	}
	
	/** Returns whether the followingSize is already known.  That
	 * is the case if either a corresponding next BreakToken or
	 * CloseBlockToken has been encountered, or if the material
	 * is known not to fit on a line.*/
	boolean followingSizeKnown() {
	    return true;
	}

	/** Indicate that the corresponding next BreakToken or
	 * CloseBlockToken has been encountered. 
	 * After this, followingSizeKnown() will return the correct value.
	 */
	void setEnd() {
	    throw new UnsupportedOperationException();
	}
	
	/** Indicate that the followingSize is guaranteed to be larger than
	 * the line width, and that it can thus be set to some large value.
	 */
	void setInfiniteSize() {
	    throw new UnsupportedOperationException();
	}
    }

    /** A token corresponding to a <code>print</code> call. */
    private class StringToken extends StreamToken {
	String s;
	
	StringToken(String s) {
	    this.s = s;
	}
	
	void print() 
	    throws IOException
	{
	    out.print(s);
	}

	int size() {
	    return back.measure(s);
	}
    }

    /** A token corresponding to an <code>ind</code> call. */
    private class IndentationToken extends StreamToken {
	protected int width;
	protected int offset;

	IndentationToken(int width, int offset) {
	    this.width = width;
	    this.offset = offset;
	}
	
	void print() 
	    throws IOException
	{
	    out.indent(width,offset);
	}
	
	int size() {
	    return width;
	}
    }

    /** Superclass of tokens which calculate their followingSize. */
    private abstract class SizeCalculatingToken extends StreamToken {
	protected int begin=0;
	/** negative means that end has not been set yet.*/
 	protected int end=-1;

	SizeCalculatingToken() {
	    begin = totalSize;
	}

	int followingSize() {
	    return end-begin;
	}

	boolean followingSizeKnown() {
	    return end>=0;
	}

	void setEnd() {
	    this.end = totalSize;
	}

	void setInfiniteSize() {
	    end = begin+largeSize;
	}
    }

    /** A token corresponding to a <code>brk</code> call. */
    private class BreakToken extends SizeCalculatingToken {
	protected int width;
	protected int offset;

	BreakToken(int width,int offset) {
	    this.width = width;
	    this.offset = offset;
	}

	int size() {
	    return width;
	}

	void print() 
	    throws IOException
	{
	    out.printBreak(width,offset,followingSize());
	}

    }

    /** A token corresponding to a <code>begin</code> call. */
    private class OpenBlockToken extends SizeCalculatingToken {
	protected boolean consistent;
	protected int indent;

	OpenBlockToken(boolean consistent,int indent) {
	    this.consistent = consistent;
	    this.indent = indent;
	}

	int size() {
	    return 0;
	}

	void print() 	    
	    throws IOException
	{
	    out.openBlock(consistent,indent,followingSize());
	}
    }

    /** A token corresponding to an <code>end</code> call. */
    private class CloseBlockToken extends StreamToken {

	CloseBlockToken() {
	}

	void print()
	    throws IOException
	{
	    out.closeBlock();
	}

	int size() {
	    return 0;
	}

    }

    /** A token corresponding to a <code>mark</code> call. */
    private class MarkToken extends StreamToken {
	protected Object o;

	MarkToken(Object o) {
	    this.o = o;
	}

	int size() {
	    return 0;
	}

	void print() 
	{
	    out.mark(o);
	}
    }
    
}