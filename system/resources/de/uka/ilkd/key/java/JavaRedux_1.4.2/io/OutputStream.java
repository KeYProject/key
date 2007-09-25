


package java.io;
public abstract class OutputStream {
    public OutputStream() {}
    public abstract void write(int b) throws IOException;
    public void write(byte[] b) throws IOException, NullPointerException {}
    public void write(byte[] b, int off, int len)
     throws IOException, NullPointerException, IndexOutOfBoundsException {}
    public void flush() throws IOException {}
    public void close() throws IOException {}
}
