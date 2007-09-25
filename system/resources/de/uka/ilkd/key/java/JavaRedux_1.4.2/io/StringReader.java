

package java.io;
public class StringReader extends Reader {
    public StringReader(String buffer) {}

    public void close() {}

    public void mark(int readAheadLimit) throws IOException {}

    public boolean markSupported() {}

    public int read() throws IOException {}

    public int read(char[] b, int off, int len) throws IOException {}
    public boolean ready() throws IOException {}
    public void reset() throws IOException {}
    public long skip(long n) throws IOException {}
}
