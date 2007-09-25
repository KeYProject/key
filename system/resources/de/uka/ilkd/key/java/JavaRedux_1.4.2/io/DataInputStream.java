

package java.io;
public class DataInputStream extends FilterInputStream implements DataInput {
    boolean ignoreInitialNewline = false;
    byte[] buf = new byte[8];
    public DataInputStream(InputStream in) {}
    public final int read(byte[] b) throws IOException {}
    public final int read(byte[] b, int off, int len) throws IOException {}
    public final boolean readBoolean() throws IOException {}
    public final byte readByte() throws IOException {}
    public final char readChar() throws IOException {}
    public final double readDouble() throws IOException {}
    public final float readFloat() throws IOException {}
    public final void readFully(byte[] b) throws IOException {}
    public final void readFully(byte[] buf, int offset, int len) throws IOException {}
    public final int readInt() throws IOException {}
    public final String readLine() throws IOException {}
    public final long readLong() throws IOException {}
    public final short readShort() throws IOException {}
    public final int readUnsignedByte() throws IOException {}
    public final int readUnsignedShort() throws IOException {}
    public final String readUTF() throws IOException {}
    public final static String readUTF(DataInput in) throws IOException {}
    public final int skipBytes(int n) throws IOException {}

    static boolean convertToBoolean(int b) throws EOFException {}

    static byte convertToByte(int i) throws EOFException {}

    static int convertToUnsignedByte(int i) throws EOFException {}

    static char convertToChar(byte[] buf) {}

    static short convertToShort(byte[] buf) {}

    static int convertToUnsignedShort(byte[] buf) {}

    static int convertToInt(byte[] buf) {}

    static long convertToLong(byte[] buf) {}
    static String convertFromUTF(byte[] buf)
     throws EOFException, UTFDataFormatException {}
}
