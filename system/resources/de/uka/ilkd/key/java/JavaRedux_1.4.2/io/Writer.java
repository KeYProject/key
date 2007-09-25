


package java.io;
public abstract class Writer {
    protected Object lock;
    protected Writer() {}
    protected Writer(Object lock) {}
    public abstract void flush() throws IOException;
    public abstract void close() throws IOException;
    public void write(int b) throws IOException {}
    public void write(char[] buf) throws IOException {}
    public abstract void write(char[] buf, int offset, int len)
     throws IOException;
    public void write(String str) throws IOException {}
    public void write(String str, int offset, int len) throws IOException {}
}
