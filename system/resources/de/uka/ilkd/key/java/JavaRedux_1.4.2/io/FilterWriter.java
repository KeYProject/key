


package java.io;
public abstract class FilterWriter extends Writer {
    protected Writer out;
    protected FilterWriter(Writer out) {}
    public void close() throws IOException {}
    public void flush() throws IOException {}
    public void write(int b) throws IOException {}
    public void write(char[] buf, int offset, int len) throws IOException {}
    public void write(String str, int offset, int len) throws IOException {}
}
