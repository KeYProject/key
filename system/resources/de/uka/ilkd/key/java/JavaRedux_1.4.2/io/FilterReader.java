


package java.io;
public abstract class FilterReader extends Reader {
    protected Reader in;
    protected FilterReader(Reader in) {}
    public void mark(int readlimit) throws IOException {}
    public boolean markSupported() {}
    public void reset() throws IOException {}
    public boolean ready() throws IOException {}
    public long skip(long num_chars) throws IOException {}
    public int read() throws IOException {}
    public int read(char[] buf, int offset, int len) throws IOException {}
    public void close() throws IOException {}
}
