


package java.io;
public class PipedWriter extends Writer {
    PipedReader sink;
    boolean closed;
    char[] read_buf = new char[1];
    public PipedWriter() {}
    public PipedWriter(PipedReader sink) throws IOException {}
    public void connect(PipedReader sink) throws IOException {}
    public void write(int b) throws IOException {}
    public void write(char[] b, int off, int len) throws IOException {}
    public void flush() throws IOException {}
    public void close() throws IOException {}
}
