

package java.io;
public class PushbackInputStream extends FilterInputStream {
    protected byte[] buf;
    protected int pos;
    public PushbackInputStream(InputStream in) {}
    public PushbackInputStream(InputStream in, int size) {}
    public int available() throws IOException {}
    public synchronized void close() throws IOException {}
    public boolean markSupported() {}
    public void reset() throws IOException {}
    public synchronized int read() throws IOException {}
    public synchronized int read(byte[] b, int off, int len) throws IOException {}
    public synchronized void unread(int b) throws IOException {}
    public synchronized void unread(byte[] b) throws IOException {}
    public synchronized void unread(byte[] b, int off, int len)
     throws IOException {}
    public synchronized long skip(long n) throws IOException {}
}
