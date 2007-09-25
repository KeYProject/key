


package java.io;
public class FilterOutputStream extends OutputStream {
    protected OutputStream out;
    public FilterOutputStream(OutputStream out) {}
    public void close() throws IOException {}
    public void flush() throws IOException {}
    public void write(int b) throws IOException {}
    public void write(byte[] buf) throws IOException {}
    public void write(byte[] buf, int offset, int len) throws IOException {}
}
