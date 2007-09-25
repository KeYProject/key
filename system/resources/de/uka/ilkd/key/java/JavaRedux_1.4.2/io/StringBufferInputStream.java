


package java.io;
public class StringBufferInputStream extends InputStream {
    protected String buffer;
    protected int pos = 0;
    protected int count;
    public StringBufferInputStream(String s) {}
    public int available() {}
    public int read() {}
    public int read(byte[] b, int off, int len) {}
    public void reset() {}
    public long skip(long n) {}
}
