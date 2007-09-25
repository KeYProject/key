


package java.io;
public class CharArrayWriter extends Writer {
    public CharArrayWriter() {}
    public CharArrayWriter(int size) {}
    public void close() {}
    public void flush() {}
    public void reset() {}
    public int size() {}
    public char[] toCharArray() {}
    public String toString() {}
    public void write(int oneChar) {}
    public void write(char[] buffer, int offset, int len) {}
    public void write(String str, int offset, int len) {}
    public void writeTo(Writer out) throws IOException {}
    private final void resize(int len) {}
    protected char[] buf;
    protected int count;
}
