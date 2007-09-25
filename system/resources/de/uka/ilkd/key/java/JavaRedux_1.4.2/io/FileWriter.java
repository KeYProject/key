


package java.io;
public class FileWriter extends OutputStreamWriter {
    public FileWriter(File file) throws SecurityException, IOException {}
    public FileWriter(File file, boolean append) throws IOException {}
    public FileWriter(FileDescriptor fd) throws SecurityException {}
    public FileWriter(String name) throws IOException {}
    public FileWriter(String name, boolean append) throws IOException {}
}
