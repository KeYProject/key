/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.pp;

import java.util.*;
import javax.annotation.Nonnull;

/**
 * This class pretty-prints information using line breaks and indentation. For instance, it can be
 * used to print
 *
 * <pre>
 * while (i > 0) {
 *     i--;
 *     j++;
 * }
 * </pre>
 *
 * instead of
 *
 * <pre>
 * while (i > 0) {
 *     i--;
 *     j++;
 * }
 * </pre>
 *
 * if a maximum line width of 15 characters is chosen.
 *
 * <P>
 * The formatted output is directed to a <em>backend</em> which might write it to an I/O stream,
 * append it to the text of a GUI component or store it in a string. The {@link Backend} interface
 * encapsulates the concept of backend. Apart from handling the output, the backend is also asked
 * for the available line width and for the amount of space needed to print a string. This makes it
 * possible to include e.g. HTML markup in the output which does not take up any space. There is
 * a convenience implementation {@link StringBackend}, which writes to a {@link java.lang.String}.
 *
 * <P>
 * The layouter internally keeps track of a current <em>indentation level</em>. Think of nicely
 * indented Java source code. Then the indentation level at any point is the number of blank columns
 * to be inserted at the beginning of the next line if you inserted a line break. To increase the
 * indentation level of parts of the text, the input to the layouter is separated into
 * <em>blocks</em>. The indentation level changes when a block is begun, and it is reset to its
 * previous value when a block is ended. Of course, blocks maybe nested.
 *
 * <P>
 * In order to break text among several lines, the layouter needs to be told where line breaks are
 * allowed. A <em>break</em> is a position in the text where there is either a line break (with
 * appropriate indentation) or a number of spaces, if enough material fits in one line. In order to
 * handle the indentation level properly, breaks should only occur inside blocks. There are in fact
 * two kinds of blocks: <em>consistent</em> and <em>inconsistent</em> ones. In a consistent block,
 * line are broken either at all or at none of the breaks. In an inconsistent block, as much
 * material as possible is put on one line before it is broken.
 *
 * <P>
 * Consider the program above. It should be printed either as
 *
 * <pre>
 * while (i > 0) {
 *     i--;
 *     j++;
 * }
 * </pre>
 *
 * or, if there is not enough space on the line, as
 *
 * <pre>
 * while (i > 0) {
 *     i--;
 *     j++;
 * }
 * </pre>
 *
 * Given a Layouter object <code>l</code>, we could say:
 *
 * <pre>
 * l.begin(true, 2).print("while (i>0) {").brk(1, 0).print("i--;").brk(1, 0).print("j++;")
 *         .brk(1, -2).print("{").end();
 * </pre>
 *
 * The call to {@link #begin(boolean,int)} starts a consistent block, increasing the indentation
 * level by 2. The {@link #print(String)} methods gives some actual text to be output. The call to
 * {@link #brk(int,int)} inserts a break. The first argument means that one space should be printed
 * at this position if the line is <em>not</em> broken. The second argument is an offset to be added
 * to the indentation level for the next line, if the line <em>is</em> broken. The effect of this
 * parameter can be seen in the call <code>brk(1,-2)</code>. The offset of <code>-2</code> outdents
 * the last line by 2 positions, which aligns the closing brace with the <code>with</code>.
 *
 * <p>
 * If the lines in a block are broken, one sometimes wants to insert spaces up to the current
 * indentation level at a certain position without allowing a line break there. This can be done
 * using the {@link #ind(int,int)} method. For instance, one wants to output either
 *
 * <pre>
 *   ...[Good and Bad and Ugly]...
 * </pre>
 *
 * or
 *
 * <pre>
 *   ...[    Good
 *       and Bad
 *       and Ugly]...
 * </pre>
 *
 * Note the four spaces required before <code>Good</code>. We do this by opening a block which sets
 * the indentation level to the column where the <code>G</code> ends up and outdenting the lines
 * with the <code>and</code>:
 *
 * <pre>
 * l.print("...[").begin(true, 4).ind(0, 0).print("Good").brk(1, -4).print("and ").print("Bad")
 *         .brk(1, -4).print("and ").print("Ugly").end().print("]...");
 * </pre>
 *
 * Again, the first argument to {@link #ind(int,int)} is a number of spaces to print if the block we
 * are in is printed on one line. The second argument is an offset to be added to the current
 * indentation level to determine the column to which we should skip.
 *
 * <p>
 * When all text has been sent to a Layouter and all blocks have been ended, the {@link #close()}
 * method should be closed. This sends all pending output to the backend and invokes the
 * {@link Backend#close()} method, which usually closes I/O streams, etc.
 *
 * <p>
 * Some applications need to keep track of where certain parts of the input text end up in the
 * output. For this purpose, the Layouter class provides the {@link #mark(Object)} method.
 *
 * <P>
 * The public methods of this class may be divided into two categories: A small number of
 * <em>primitive</em> methods, as described above, and a host of <em>convenience</em> methods which
 * simplify calling the primitive ones for often-used arguments. For instance a call to
 * {@link #beginC()} is shorthand for <code>begin(true,ind)</code>, where <code>ind</code> is the
 * default indentation selected when the Layouter was constructed.
 *
 * <P>
 * Most of the methods can throw an {@link UnbalancedBlocksException}, which indicates that the
 * sequence of method calls was illegal, i.e. more blocks were ended than begun, the Layouter is
 * closed before all blocks are ended, a break occurs outside any block, etc.
 *
 * <P>
 * Also, most methods can throw an {@link java.io.IOException}. This only happens if a called method
 * in the backend throws an IOException, in which case that exception is passed through to the
 * caller of the Layouter method.
 *
 * @author Martin Giese
 * @see Backend
 */



/*
 * Implementation note: The name of this class is actually a lie. What this class does is calculate
 * the space needed by blocks and portions of blocks between breaks if they are printed in a
 * single line. The actual laying out, that is choosing whether to break line or not is done by a
 * Printer object, which in turn sends its output to the Backend.
 *
 */

public class Layouter<M> {

    /** The Printer used for output. */
    private final Printer<M> out;

    /** The list of scanned tokens not yet output. */
    private final Queue<StreamToken<M>> queue = new ArrayDeque<>();

    /**
     * A stack of <code>OpenBlockToken</code>s and <code>BreakToken</code>s in <code>stream</code>,
     * waiting for their size to be determined.
     */
    private final Deque<StreamToken<M>> delimStack = new ArrayDeque<>();

    /*
     * Some Invariants:
     *
     * delimStack.isEmpty() implies stream.isEmpty()
     *
     * Any OpenBlockToken in stream is also on the delimStack. The latest BreakToken of any open
     * block in the stream is also on the delim stack.
     *
     */


    /**
     * Total size of received strings and blanks, if they were printed in one line. The difference
     * of this between two states says how much space would be needed to print the intervening stuff
     * without line breaks.
     */
    private int totalSize = 0;

    /**
     * Total size of strings and blanks sent to the Printer <code>out</code>. Subtract this from
     * <code>totalOutput</code> and you get the space needed to print what is still buffered in
     * <code>stream</code>
     */
    private int totalOutput = 0;

    /**
     * The size assigned to things which are guaranteed not to fit on a line. For good measure, this
     * is initialized to twice the line width by the constructors.
     */
    private final int largeSize;

    /** A default indentation value used for blocks. */
    private final int defaultIndent;


    // PRIMITIVE CONSTRUCTOR -------------------------------------------

    /**
     * Constructs a newly allocated Layouter which will send output to the given {@link Backend} and
     * has the given default indentation.
     *
     * @param back the Backend
     * @param indentation the default indentation
     *
     */

    public Layouter(StringBackend<M> back, int lineWidth, int indentation) {
        out = new Printer<>(back, lineWidth);
        largeSize = 2 * lineWidth;
        this.defaultIndent = indentation;
    }

    /** Line width */
    public int lineWidth() {
        return out.lineWidth();
    }

    /** Sets the line width */
    public void setLineWidth(int lineWidth) {
        out.setLineWidth(lineWidth);
    }

    /** Default indent */
    public int defaultIndent() {
        return defaultIndent;
    }

    public StringBackend<M> backend() {
        return out.backend();
    }

    public String result() {
        return out.result();
    }

    // PRIMITIVE STREAM OPERATIONS ------------------------------------

    /**
     * Output text material. The string <code>s</code> should not contain newline characters. If you
     * have a string with newline characters, and want to retain its formatting, consider using the
     * {@link #pre(String s)} method. The Layouter will not insert any line breaks in such a string.
     *
     * @param s the String to print.
     * @return this
     */
    public Layouter<M> print(String s) {
        if (delimStack.isEmpty()) {
            out.print(s);
            totalSize += s.length();
            totalOutput += s.length();
        } else {
            enqueue(new StringToken<>(s));
            totalSize += s.length();

            while (totalSize - totalOutput > out.space() && !delimStack.isEmpty()) {
                popBottom().setInfiniteSize(largeSize);
                advanceLeft();
            }
        }
        return this;
    }

    /**
     * Begin a block. If <code>consistent</code> is set, breaks are either all broken or all not
     * broken. The indentation level is increased by <code>indent</code>.
     *
     * @param consistent <code>true</code> for consistent block
     * @param relative <code>true</code> for indentation relative to parent block
     * @param indent increment to indentation level
     * @return this
     */
    public Layouter<M> begin(boolean consistent, boolean relative, int indent) {
        StreamToken<M> t = new OpenBlockToken<>(totalSize, consistent, relative, indent);
        enqueue(t);
        push(t);
        return this;
    }

    /**
     * Ends the innermost block.
     *
     * @return this
     **/
    public Layouter<M> end() {
        if (delimStack.isEmpty()) {
            /* then stream is also empty, so output */
            out.closeBlock();
        } else {
            enqueue(new CloseBlockToken<>());

            StreamToken<M> topDelim = pop();
            topDelim.setEnd(totalSize);
            if (topDelim instanceof BreakToken && !delimStack.isEmpty()) {
                /* This must be the matching OpenBlockToken */
                StreamToken<M> topOpen = pop();
                topOpen.setEnd(totalSize);
            }

            if (delimStack.isEmpty()) {
                /* preserve invariant */
                advanceLeft();
            }
        }
        return this;
    }

    /**
     * Print a break. This will print <code>width</code> spaces if the line is <em>not</em> broken
     * at this point. If it <em>is</em> broken, indentation is added to the current indentation
     * level, plus the value of <code>offset</code>.
     *
     * @param width space to insert if not broken
     * @param offset offset relative to current indentation level
     * @return this
     */
    public Layouter<M> brk(int width, int offset) {
        if (!delimStack.isEmpty()) {
            StreamToken<M> s = top();
            if (s instanceof BreakToken) {
                pop();
                s.setEnd(totalSize);
            }
        }

        StreamToken<M> t = new BreakToken<>(totalSize, width, offset);
        enqueue(t);
        push(t);
        totalSize += width;
        return this;
    }

    /**
     * Indent to a current indentation level if surrounding block is broken. If the surrounding
     * block fits on one line, insert <code>width</code> spaces. Otherwise, indent to the current
     * indentation level, plus <code>offset</code>, unless that position has already been exceeded
     * on the current line. If that is the case, nothing is printed. No line break is possible at
     * this point.
     *
     * @param width space to insert if not broken
     * @param offset offset relative to current indentation level
     * @return this
     */
    public Layouter<M> ind(int width, int offset) {
        if (delimStack.isEmpty()) {
            out.indent(width, offset);
            totalSize += width;
            totalOutput += width;
        } else {
            enqueue(new IndentationToken<>(width, offset));
            totalSize += width;
        }
        return this;
    }

    /**
     * This leads to a call of the {@link Backend#mark(Object)} method of the backend, when the
     * material preceding the call to <code>mark</code> has been printed to the backend, including
     * any inserted line breaks and indentation. The {@link Object} argument to <code>mark</code> is
     * passed through unchanged to the backend and may be used by the application to pass
     * information about the purpose of the mark.
     *
     * @param o an object to be passed through to the backend.
     * @return this
     *
     */
    public Layouter<M> mark(M o) {
        if (delimStack.isEmpty()) {
            out.mark(o);
        } else {
            enqueue(new MarkToken<>(o));
        }
        return this;
    }

    /**
     * Close the Layouter. No more methods should be called after this. All blocks begun must have
     * been ended by this point. Any pending material is written to the backend.
     *
     */
    public void close() {
        if (!delimStack.isEmpty()) {
            throw new UnbalancedBlocksException();
        } else {
            advanceLeft();
        }
    }


    // CONVENIENCE STREAM OPERATIONS ---------------------------------

    /**
     * Begin a block. If <code>consistent</code> is set, breaks are either all broken or all not
     * broken. The indentation level is increased by <code>indent</code>.
     *
     * @param consistent <code>true</code> for consistent block
     * @param indent increment to indentation level
     * @return this
     */
    public Layouter<M> begin(boolean consistent, int indent) {
        return begin(consistent, false, indent);
    }

    /**
     * Begin a relative block. If <code>consistent</code> is set, breaks are either all broken or
     * all not
     * broken. The indentation level is increased by <code>indent</code>.
     *
     * @param consistent <code>true</code> for consistent block
     * @param indent increment to indentation level
     * @return this
     */
    public Layouter<M> beginRelative(boolean consistent, int indent) {
        return begin(consistent, true, indent);
    }

    /**
     * Begin a relative inconsistent block. Add this Layouter's default indentation to the
     * indentation
     * level.
     *
     * @return this
     */
    public Layouter<M> beginRelativeI() {
        return beginRelative(false, defaultIndent);
    }

    /**
     * Begin a relative inconsistent block. Add this Layouter's default indentation to the
     * indentation
     * level.
     *
     * @return this
     */
    public Layouter<M> beginRelativeC() {
        return beginRelative(true, defaultIndent);
    }

    /**
     * Begin a relative inconsistent block. Add this Layouter's default indentation to the
     * indentation
     * level.
     *
     * @param indent the indentation for this block
     * @return this
     */
    public Layouter<M> beginRelativeC(int indent) {
        return beginRelative(true, indent);
    }

    /**
     * Begin an inconsistent block. Add this Layouter's default indentation to the indentation
     * level.
     *
     * @return this
     */
    public Layouter<M> beginI() {
        return begin(false, defaultIndent);
    }

    /**
     * Begin a consistent block. Add this Layouter's default indentation to the indentation level.
     *
     * @return this
     */
    public Layouter<M> beginC() {
        return begin(true, defaultIndent);
    }

    /**
     * Begin an inconsistent block. Add <code>indent</code> to the indentation level.
     *
     * @param indent the indentation for this block
     * @return this
     */
    public Layouter<M> beginI(int indent) {
        return begin(false, indent);
    }

    /**
     * Begin a consistent block. Add <code>indent</code> to the indentation level.
     *
     * @param indent the indentation for this block
     * @return this
     */
    public Layouter<M> beginC(int indent) {
        return begin(true, indent);
    }

    /**
     * Begin a block with default indentation. Add this Layouter's default indentation to the
     * indentation level.
     *
     * @param consistent <code>true</code> for consistent block
     * @return this
     */
    public Layouter<M> begin(boolean consistent) {
        return begin(consistent, defaultIndent);
    }


    /**
     * Print a break with zero offset.
     *
     * @param width space to insert if not broken
     * @return this
     */
    public Layouter<M> brk(int width) {
        return brk(width, 0);
    }

    /**
     * Print a break with zero offset and width one.
     *
     * @return this
     */
    public Layouter<M> brk() {
        return brk(1);
    }

    /**
     * Print a break with zero offset and large width. As the large number of spaces will never fit
     * into one line, this amounts to a forced line break.
     *
     * @return this
     */
    public Layouter<M> nl() {
        return brk(largeSize);
    }

    /**
     * Indent with zero offset and zero width. Just indents to the current indentation level if the
     * block is broken, and prints nothing otherwise.
     *
     * @return this
     */
    public Layouter<M> ind() {
        return this.ind(0, 0);
    }


    /**
     * Layout preformatted text. This amounts to a (consistent) block with indentation 0, where each
     * line of <code>s</code> (separated by \n) gets printed as a string and newlines become forced
     * breaks.
     *
     * @param s the pre-formatted string
     * @return this
     */
    public Layouter<M> pre(String s) {
        StringTokenizer st = new StringTokenizer(s, "\n", true);
        beginC(0);
        while (st.hasMoreTokens()) {
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
    private void push(StreamToken<M> t) {
        delimStack.offerLast(t);
    }

    /** Pop the topmost Token from the delimStack */
    private StreamToken<M> pop() {
        StreamToken<M> token = delimStack.pollLast();
        if (token == null) {
            throw new UnbalancedBlocksException();
        }
        return token;
    }

    /**
     * Remove and return the token from the <em>bottom</em> of the delimStack
     */
    private @Nonnull StreamToken<M> popBottom() {
        StreamToken<M> token = delimStack.pollFirst();
        if (token == null) {
            throw new UnbalancedBlocksException();
        }
        return token;
    }

    /** Return the top of the delimStack, without popping it. */
    private StreamToken<M> top() {
        StreamToken<M> token = delimStack.peekLast();
        if (token == null) {
            throw new UnbalancedBlocksException();
        }
        return token;
    }


    /* stream handling */

    /** Put a StreamToken into the stream (at the end). */
    private void enqueue(StreamToken<M> t) {
        queue.offer(t);
    }

    /**
     * Send tokens from <code>stream<code> to <code>out</code> as long as there are tokens left and
     * their size is known.
     */
    private void advanceLeft() {
        StreamToken<M> t;
        while (!queue.isEmpty() && ((t = queue.peek()).followingSizeKnown())) {
            t.print(out);
            queue.poll();
            totalOutput += t.size();
        }
    }

    // STREAM TOKEN CLASSES -----------------------------------------

    /**
     * A stream token.
     */
    private static abstract class StreamToken<M> {
        /** Send this token to the Printer {@link #out}. */
        abstract void print(Printer<M> out);

        /** Return the size of this token if the block is not broken. */
        abstract int size();

        /**
         * Returns whether the followingSize is already known. That is the case if either a
         * corresponding next BreakToken or CloseBlockToken has been encountered, or if the material
         * is known not to fit on a line.
         */
        boolean followingSizeKnown() {
            return true;
        }

        /**
         * Indicate that the corresponding next BreakToken or CloseBlockToken has been encountered.
         * After this, followingSizeKnown() will return the correct value.
         */
        void setEnd(int end) {
            throw new UnsupportedOperationException();
        }

        /**
         * Indicate that the followingSize is guaranteed to be larger than the line width, and that
         * it can thus be set to some large value.
         */
        void setInfiniteSize(int large) {
            throw new UnsupportedOperationException();
        }
    }

    /** A token corresponding to a <code>print</code> call. */
    private static class StringToken<M> extends StreamToken<M> {
        final String s;

        StringToken(String s) {
            this.s = s;
        }

        void print(Printer<M> out) {
            out.print(s);
        }

        int size() {
            return s.length();
        }
    }

    /** A token corresponding to an <code>ind</code> call. */
    private static class IndentationToken<M> extends StreamToken<M> {
        protected final int width;
        protected final int offset;

        IndentationToken(int width, int offset) {
            this.width = width;
            this.offset = offset;
        }

        void print(Printer<M> out) {
            out.indent(width, offset);
        }

        int size() {
            return width;
        }
    }

    /** Superclass of tokens which calculate their followingSize. */
    private static abstract class SizeCalculatingToken<M> extends StreamToken<M> {
        protected final int begin;
        /** negative means that end has not been set yet. */
        protected int end = -1;

        SizeCalculatingToken(int begin) {
            this.begin = begin;
        }

        int followingSize() {
            return end - begin;
        }

        @Override
        boolean followingSizeKnown() {
            return end >= 0;
        }

        @Override
        void setEnd(int end) {
            this.end = end;
        }

        @Override
        void setInfiniteSize(int large) {
            end = begin + large;
        }
    }

    /** A token corresponding to a <code>brk</code> call. */
    private static class BreakToken<M> extends SizeCalculatingToken<M> {
        protected final int width;
        protected final int offset;

        BreakToken(int begin, int width, int offset) {
            super(begin);
            this.width = width;
            this.offset = offset;
        }

        int size() {
            return width;
        }

        void print(Printer<M> out) {
            out.printBreak(width, offset, followingSize());
        }
    }

    /** A token corresponding to a <code>begin</code> call. */
    private static class OpenBlockToken<M> extends SizeCalculatingToken<M> {
        protected final boolean consistent;
        protected final boolean relative;
        protected final int indent;

        OpenBlockToken(int begin, boolean consistent, boolean relative, int indent) {
            super(begin);
            this.consistent = consistent;
            this.relative = relative;
            this.indent = indent;
        }

        int size() {
            return 0;
        }

        void print(Printer<M> out) {
            out.openBlock(consistent, relative, indent, followingSize());
        }
    }

    /** A token corresponding to an <code>end</code> call. */
    private static class CloseBlockToken<M> extends StreamToken<M> {
        CloseBlockToken() {}

        void print(Printer<M> out) {
            out.closeBlock();
        }

        int size() {
            return 0;
        }

    }

    /** A token corresponding to a <code>mark</code> call. */
    private static class MarkToken<M> extends StreamToken<M> {
        protected final M o;

        MarkToken(M o) {
            this.o = o;
        }

        int size() {
            return 0;
        }

        void print(Printer<M> out) {
            out.mark(o);
        }
    }
}
