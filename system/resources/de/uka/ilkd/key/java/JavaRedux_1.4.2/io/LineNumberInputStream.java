


package java.io;
public class LineNumberInputStream extends FilterInputStream {
    public LineNumberInputStream(InputStream in) {}
    public int available() throws IOException {}
    public int getLineNumber() {}
    public void mark(int readlimit) {}
    public int read() throws IOException {}
    public int read(byte[] b, int off, int len) throws IOException {}
    public void reset() throws IOException {}
    public void setLineNumber(int lineNumber) {}
    public long skip(long n) throws IOException {}
}
