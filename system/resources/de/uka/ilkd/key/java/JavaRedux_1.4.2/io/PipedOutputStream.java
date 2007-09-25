


package java.io;
public class PipedOutputStream extends OutputStream {
    PipedInputStream sink;
    boolean closed;
    public PipedOutputStream() {}
    public PipedOutputStream(PipedInputStream sink) throws IOException {}
    public void connect(PipedInputStream sink) throws IOException {}
    public void write(int b) throws IOException {}
    public void write(byte[] b, int off, int len) throws IOException {}
    public void flush() throws IOException {}
    public void close() throws IOException {}
}
