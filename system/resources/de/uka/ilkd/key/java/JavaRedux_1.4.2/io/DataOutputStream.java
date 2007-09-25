


package java.io;
public class DataOutputStream extends FilterOutputStream implements DataOutput {
    protected int written;
    public DataOutputStream(OutputStream out) {}
    public void flush() throws IOException {}
    public final int size() {}
    public synchronized void write(int value) throws IOException {}
    public synchronized void write(byte[] buf, int offset, int len)
     throws IOException {}
    public final void writeBoolean(boolean value) throws IOException {}
    public final void writeByte(int value) throws IOException {}
    public final synchronized void writeShort(int value) throws IOException {}
    public final synchronized void writeChar(int value) throws IOException {}
    public final synchronized void writeInt(int value) throws IOException {}
    public final synchronized void writeLong(long value) throws IOException {}
    public final void writeFloat(float value) throws IOException {}
    public final void writeDouble(double value) throws IOException {}
    public final void writeBytes(String value) throws IOException {}
    public final void writeChars(String value) throws IOException {}
    public synchronized final void writeUTF(String value) throws IOException {}
}
