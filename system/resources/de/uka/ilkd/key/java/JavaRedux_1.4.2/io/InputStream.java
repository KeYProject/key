


package java.io;
public abstract class InputStream {
    public InputStream() {}
    public int available() throws IOException {}
    public void close() throws IOException {}
    public void mark(int readLimit) {}
    public boolean markSupported() {}
    public abstract int read() throws IOException;
    public int read(byte[] b) throws IOException {}
    public int read(byte[] b, int off, int len) throws IOException {}
    public void reset() throws IOException {}
    public long skip(long n) throws IOException {}
}
