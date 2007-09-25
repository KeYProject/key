


package java.io;
public class CharArrayReader extends Reader {
    protected char[] buf;
    protected int pos;
    protected int markedPos;
    protected int count;
    public CharArrayReader(char[] buffer) {}
    public CharArrayReader(char[] buffer, int offset, int length) {}
    public void close() {}
    public void mark(int readAheadLimit) throws IOException {}
    public boolean markSupported() {}
    public int read() throws IOException {}
    public int read(char[] b, int off, int len) throws IOException {}
    public boolean ready() throws IOException {}
    public void reset() throws IOException {}
    public long skip(long n) throws IOException {}
}
