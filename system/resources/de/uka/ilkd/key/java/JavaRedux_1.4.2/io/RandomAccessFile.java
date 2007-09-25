


package java.io;

import java.nio.channels.FileChannel;
import gnu.java.nio.channels.FileChannelImpl;
public class RandomAccessFile implements DataOutput, DataInput {
    public RandomAccessFile(File file, String mode) throws FileNotFoundException {}
    public RandomAccessFile(String fileName, String mode)
     throws FileNotFoundException {}
    public void close() throws IOException {}
    public final FileDescriptor getFD() throws IOException {}
    public long getFilePointer() throws IOException {}
    public void setLength(long newLen) throws IOException {}
    public long length() throws IOException {}
    public int read() throws IOException {}
    public int read(byte[] buffer) throws IOException {}
    public int read(byte[] buffer, int offset, int len) throws IOException {}
    public final boolean readBoolean() throws IOException {}
    public final byte readByte() throws IOException {}
    public final char readChar() throws IOException {}
    public final double readDouble() throws IOException {}
    public final float readFloat() throws IOException {}
    public final void readFully(byte[] buffer) throws IOException {}
    public final void readFully(byte[] buffer, int offset, int count)
     throws IOException {}
    public final int readInt() throws IOException {}
    public final String readLine() throws IOException {}
    public final long readLong() throws IOException {}
    public final short readShort() throws IOException {}
    public final int readUnsignedByte() throws IOException {}
    public final int readUnsignedShort() throws IOException {}
    public final String readUTF() throws IOException {}
    public void seek(long pos) throws IOException {}
    public int skipBytes(int numBytes) throws IOException {}
    public void write(int oneByte) throws IOException {}
    public void write(byte[] buffer) throws IOException {}
    public void write(byte[] buffer, int offset, int len) throws IOException {}
    public final void writeBoolean(boolean val) throws IOException {}
    public final void writeByte(int v) throws IOException {}
    public final void writeShort(int v) throws IOException {}
    public final void writeChar(int v) throws IOException {}
    public final void writeInt(int v) throws IOException {}
    public final void writeLong(long v) throws IOException {}
    public final void writeFloat(float v) throws IOException {}
    public final void writeDouble(double v) throws IOException {}
    public final void writeBytes(String s) throws IOException {}
    public final void writeChars(String s) throws IOException {}
    public final void writeUTF(String s) throws IOException {}
    public final synchronized FileChannel getChannel() {}
}
