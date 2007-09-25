


package java.io;
public class BufferedReader extends Reader {
    Reader in;
    char[] buffer;
    int pos;
    int limit;
    int markPos = -1;
    static final int DEFAULT_BUFFER_SIZE = 8192;
    public BufferedReader(Reader in) {}
    public BufferedReader(Reader in, int size) {}
    public void close() throws IOException {}
    public boolean markSupported() {}
    public void mark(int readLimit) throws IOException {}
    public void reset() throws IOException {}
    public boolean ready() throws IOException {}
    public int read(char[] buf, int offset, int count) throws IOException {}
    private int fill() throws IOException {}

    public int read() throws IOException {}
    private int lineEnd(int limit) {}
    public String readLine() throws IOException {}
    public long skip(long count) throws IOException {}

    private void checkStatus() throws IOException {}
}
