package de.uka.ilkd.key.util.pp;

import java.io.IOException;
import java.io.Writer;

/**
 * A {@link Backend} which writes all output to a java.io.Writer. The {@link #mark(Object o)} method
 * does nothing in this implementation. There is a method {@link #count()} which returns the number
 * of characters written by this so far.
 *
 * This class is the cause for numerous unnecessary "throws IOException" clauses throughout the
 * entire project. It should be removed and replaced by StringBackend. (Kai Wallisch 09/2014)
 */

@Deprecated
public class WriterBackend implements Backend {

    protected Writer out;
    protected int lineWidth;
    protected int count = 0;

    public WriterBackend(Writer w, int lineWidth) {
        this.out = w;
        this.lineWidth = lineWidth;
    }

    /**
     * Append a String <code>s</code> to the output. <code>s</code> contains no newlines.
     */
    public void print(String s) throws IOException {
        out.write(s);
        count += measure(s);
    }

    /** Start a new line. */
    public void newLine() throws IOException {
        out.write('\n');
        count++;
    }

    /** Closes this backend */
    public void close() throws IOException {
        out.close();
    }

    /** Flushes any buffered output */
    public void flush() throws IOException {
        out.flush();
    }

    /** Gets called to record a <code>mark()</code> call in the input. */
    public void mark(Object o) {
        return;
    }

    /** Returns the number of characters written through this backend. */
    public int count() {
        return count;
    }

    /** Returns the available space per line */
    public int lineWidth() {
        return lineWidth;
    }

    /** Returns the space required to print the String <code>s</code> */
    public int measure(String s) {
        return s.length();
    }

}
