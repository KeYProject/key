

package java.io;
public class PipedInputStream extends InputStream {
    PipedOutputStream source;
    boolean closed;
    protected static final int PIPE_SIZE = 1024;
    protected byte[] buffer = new byte[PIPE_SIZE];
    protected int in = -1;
    protected int out = 0;
    public PipedInputStream() {}
    public PipedInputStream(PipedOutputStream source) throws IOException {}
    public void connect(PipedOutputStream source) throws IOException {}
    protected synchronized void receive(int b) throws IOException {}
    synchronized void receive(byte[] buf, int offset, int len)
     throws IOException {}
    public int read() throws IOException {}
    public synchronized int read(byte[] buf, int offset, int len)
     throws IOException {}
    public synchronized int available() throws IOException {}
    public synchronized void close() throws IOException {}
}
