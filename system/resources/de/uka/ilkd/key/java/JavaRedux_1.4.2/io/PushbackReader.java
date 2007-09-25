


package java.io;
public class PushbackReader extends FilterReader {
    public PushbackReader(Reader in) {}
    public PushbackReader(Reader in, int bufsize) {}
    public void close() throws IOException {}
    public void mark(int read_limit) throws IOException {}
    public boolean markSupported() {}
    public void reset() throws IOException {}
    public boolean ready() throws IOException {}
    public long skip(long num_chars) throws IOException {}
    public int read() throws IOException {}
    public synchronized int read(char[] buffer, int offset, int length)
     throws IOException {}
    public void unread(int b) throws IOException {}
    public synchronized void unread(char[] buf) throws IOException {}
    public synchronized void unread(char[] buffer, int offset, int length)
     throws IOException {}
}
