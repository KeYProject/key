


package java.io;
public class BufferedInputStream extends FilterInputStream {
    protected byte[] buf;
    protected int count;
    protected int pos;
    protected int markpos = -1;
    protected int marklimit;
    public BufferedInputStream(InputStream in) {}
    public BufferedInputStream(InputStream in, int size) {}
    public synchronized int available() throws IOException {}
    public void close() throws IOException {}
    public synchronized void mark(int readlimit) {}
    public boolean markSupported() {}
    public synchronized int read() throws IOException {}
    public synchronized int read(byte[] b, int off, int len) throws IOException {}
    public synchronized void reset() throws IOException {}
    public synchronized long skip(long n) throws IOException {}
    private boolean refill() throws IOException {}
}
