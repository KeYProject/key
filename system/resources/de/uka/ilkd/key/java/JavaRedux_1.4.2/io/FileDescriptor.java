


package java.io;

import java.nio.channels.ByteChannel;
import java.nio.channels.FileChannel;
public final class FileDescriptor {
    public static final FileDescriptor in;
    public static final FileDescriptor out;
    public static final FileDescriptor err;

    final ByteChannel channel;
    public FileDescriptor() {}
    FileDescriptor(ByteChannel channel) {}
    public void sync() throws SyncFailedException {}
    public boolean valid() {}
}
