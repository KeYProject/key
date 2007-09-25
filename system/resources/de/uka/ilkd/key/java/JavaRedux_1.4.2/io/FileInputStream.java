


package java.io;

import java.nio.channels.FileChannel;
import gnu.java.nio.channels.FileChannelImpl;
public class FileInputStream extends InputStream {
    public FileInputStream(String name) throws FileNotFoundException {}
    public FileInputStream(File file) throws FileNotFoundException {}
    public FileInputStream(FileDescriptor fdObj) {}

    FileInputStream(FileChannelImpl ch) {}
    public int available() throws IOException {}
    public void close() throws IOException {}

    protected void finalize() throws IOException {}
    public final FileDescriptor getFD() throws IOException {}
    public int read() throws IOException {}
    public int read(byte[] buf) throws IOException {}
    public int read(byte[] buf, int offset, int len) throws IOException {}
    public synchronized long skip(long numBytes) throws IOException {}
    public synchronized FileChannel getChannel() {}
}
