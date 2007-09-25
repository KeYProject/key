


package java.io;

import java.util.Enumeration;
public class SequenceInputStream extends InputStream {
    public SequenceInputStream(Enumeration e) {}
    public SequenceInputStream(InputStream s1, InputStream s2) {}
    public int available() throws IOException {}
    public void close() throws IOException {}
    public int read() throws IOException {}
    public int read(byte[] b, int off, int len) throws IOException {}
    private InputStream getNextStream() {}
}
