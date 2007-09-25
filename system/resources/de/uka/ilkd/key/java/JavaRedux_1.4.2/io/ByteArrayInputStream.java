


package java.io;
public class ByteArrayInputStream extends InputStream {
    protected byte[] buf;
    protected int pos;
    protected int mark;
    protected int count;
    public ByteArrayInputStream(byte[] buffer) {}
    public ByteArrayInputStream(byte[] buffer, int offset, int length) {}
    public synchronized int available() {}
    public synchronized void mark(int readLimit) {}
    public boolean markSupported() {}
    public synchronized int read() {}
    public synchronized int read(byte[] buffer, int offset, int length) {}
    public synchronized void reset() {}
    public synchronized long skip(long num) {}
}
