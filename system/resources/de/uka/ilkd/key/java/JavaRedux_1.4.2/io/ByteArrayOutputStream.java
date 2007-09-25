


package java.io;
public class ByteArrayOutputStream extends OutputStream {
    public ByteArrayOutputStream() {}
    public ByteArrayOutputStream(int size) {}
    public synchronized void reset() {}
    public int size() {}
    public synchronized byte[] toByteArray() {}
    public String toString() {}
    public String toString(String enc) throws UnsupportedEncodingException {}
    public String toString(int hibyte) {}
    private void resize(int add) {}
    public synchronized void write(int oneByte) {}
    public synchronized void write(byte[] buffer, int offset, int add) {}
    public synchronized void writeTo(OutputStream out) throws IOException {}
    protected byte[] buf;
    protected int count;

    static {}
}
