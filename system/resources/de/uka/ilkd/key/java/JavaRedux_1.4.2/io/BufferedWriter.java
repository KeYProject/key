


package java.io;
public class BufferedWriter extends Writer {
    char[] buffer;
    int count;
    public BufferedWriter(Writer out) {}
    public BufferedWriter(Writer out, int size) {}
    public void close() throws IOException {}
    public void flush() throws IOException {}
    public void newLine() throws IOException {}
    public void write(int oneChar) throws IOException {}
    public void write(char[] buf, int offset, int len) throws IOException {}
    public void write(String str, int offset, int len) throws IOException {}
    private void localFlush() throws IOException {}
}
