


package java.io;

import java.nio.channels.FileChannel;
import gnu.java.nio.channels.FileChannelImpl;
public class FileOutputStream extends OutputStream {
    public FileOutputStream(String path, boolean append) throws SecurityException, FileNotFoundException {}
    public FileOutputStream(String path) throws SecurityException, FileNotFoundException {}
    public FileOutputStream(File file) throws SecurityException, FileNotFoundException {}
    public FileOutputStream(File file, boolean append) throws FileNotFoundException {}
    public FileOutputStream(FileDescriptor fdObj) throws SecurityException {}

    FileOutputStream(FileChannelImpl ch) {}

    protected void finalize() throws IOException {}
    public final FileDescriptor getFD() throws IOException {}
    public void write(int b) throws IOException {}
    public void write(byte[] buf)
     throws IOException {}
    public void write(byte[] buf, int offset, int len)
     throws IOException {}
    public void close() throws IOException {}
    public synchronized FileChannel getChannel() {}
}
