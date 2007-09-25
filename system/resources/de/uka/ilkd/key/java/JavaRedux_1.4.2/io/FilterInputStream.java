


package java.io;
public class FilterInputStream extends InputStream {
    protected InputStream in;
    protected FilterInputStream(InputStream in) {}
    public void mark(int readlimit) {}
    public boolean markSupported() {}
    public void reset() throws IOException {}
    public int available() throws IOException {}
    public long skip(long numBytes) throws IOException {}
    public int read() throws IOException {}
    public int read(byte[] buf) throws IOException {}
    public int read(byte[] buf, int offset, int len) throws IOException {}
    public void close() throws IOException {}
}
