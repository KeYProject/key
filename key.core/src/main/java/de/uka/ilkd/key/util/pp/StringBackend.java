package de.uka.ilkd.key.util.pp;

/**
 * A {@link Backend} which appends all output to a StringBuffer. The {@link #mark(Object o)} method
 * does nothing in this implementation. There is a method {@link #count()} which returns the number
 * of characters written by this so far. The method {@link #getString()} gets the output written so
 * far.
 */
public class StringBackend implements Backend {
    protected StringBuilder out;
    protected int lineWidth;

    /**
     * Create a new StringBackend. This will accumulate output in a fresh, private StringBuffer.
     */
    public StringBackend(int lineWidth) {
        this.lineWidth = lineWidth;
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

    /** Closes this backend */
    public void close() {}

    /** Flushes any buffered output */
    public void flush() {}

    /** Gets called to record a <code>mark()</code> call in the input. */
    public void mark(Object o) {}

    /** Returns the number of characters written through this backend. */
    public int count() {
        return out.length();
    }

    /** Returns the available space per line */
    public int lineWidth() {
        return lineWidth;
    }

    /** Returns the accumulated output */
    public String getString() {
        return out.toString();
    }
}
