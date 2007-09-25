


package java.io;
public class BufferedOutputStream extends FilterOutputStream {
    protected byte[] buf;
    protected int count;
    public BufferedOutputStream(OutputStream out) {}
    public BufferedOutputStream(OutputStream out, int size) {}
    public synchronized void flush() throws IOException {}
    public synchronized void write(int b) throws IOException {}
    public synchronized void write(byte[] buf, int offset, int len)
     throws IOException {}
}
