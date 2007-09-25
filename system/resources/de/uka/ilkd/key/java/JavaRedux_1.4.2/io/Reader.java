

package java.io;
public abstract class Reader {
    protected Object lock;
    protected Reader() {}
    protected Reader(Object lock) {}
    public abstract int read(char buf[], int offset, int count)
     throws IOException;
    public int read(char buf[]) throws IOException {}
    public int read() throws IOException {}
    public abstract void close() throws IOException;
    public boolean markSupported() {}
    public void mark(int readLimit) throws IOException {}
    public void reset() throws IOException {}
    public boolean ready() throws IOException {}
    public long skip(long count) throws IOException {}
}
