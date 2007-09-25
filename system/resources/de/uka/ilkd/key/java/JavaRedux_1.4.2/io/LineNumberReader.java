

package java.io;
public class LineNumberReader extends BufferedReader {
    public LineNumberReader(Reader in) {}
    public LineNumberReader(Reader in, int size) {}
    public int getLineNumber() {}
    public void setLineNumber(int lineNumber) {}
    public void mark(int readLimit) throws IOException {}
    public void reset() throws IOException {}
    private int fill() throws IOException {}
    public int read() throws IOException {}
    public int read(char[] buf, int offset, int count) throws IOException {}

    private void skipRedundantLF() throws IOException {}
    public String readLine() throws IOException {}
    public long skip(long count) throws IOException {}
}
