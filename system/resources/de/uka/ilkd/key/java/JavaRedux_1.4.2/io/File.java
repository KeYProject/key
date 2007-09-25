


package java.io;

import java.net.MalformedURLException;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URL;
public class File implements Serializable, Comparable {
    public static final String separator = System.getProperty("file.separator");
    public static final char separatorChar = separator.charAt(0);
    public static final String pathSeparator = System.getProperty("path.separator");
    public static final char pathSeparatorChar = pathSeparator.charAt(0);
    public boolean canRead() {}
    public boolean canWrite() {}
    public boolean createNewFile() throws IOException {}
    public synchronized boolean delete() {}
    public boolean equals(Object obj) {}
    public boolean exists() {}
    public File(String name) {}
    private String normalizePath(String p) {}
    public File(String dirPath, String name) {}
    public File(File directory, String name) {}
    public File(URI uri) {}
    public String getAbsolutePath() {}
    public File getAbsoluteFile() {}
    public String getCanonicalPath() throws IOException {}
    public File getCanonicalFile() throws IOException {}
    public String getName() {}
    public String getParent() {}
    public File getParentFile() {}
    public String getPath() {}
    public int hashCode() {}
    public boolean isAbsolute() {}
    public boolean isDirectory() {}
    public boolean isFile() {}
    public boolean isHidden() {}
    public long lastModified() {}
    public long length() {}
    public String[] list(FilenameFilter filter) {}
    public String[] list() {}
    public File[] listFiles() {}
    public File[] listFiles(FilenameFilter filter) {}
    public File[] listFiles(FileFilter filter) {}
    public String toString() {}
    public URI toURI() {}
    public URL toURL() throws MalformedURLException {}
    public boolean mkdir() {}
    public boolean mkdirs() {}
    public static File createTempFile(String prefix, String suffix,
                                    File directory)
     throws IOException {}
    public boolean setReadOnly() {}
    public static File[] listRoots() {}
    public static File createTempFile(String prefix, String suffix)
     throws IOException {}
    public int compareTo(File other) {}
    public int compareTo(Object obj) {}
    public synchronized boolean renameTo(File dest) {}
    public boolean setLastModified(long time) {}

    private void checkWrite() {}

    private void checkRead() {}
    public void deleteOnExit() {}

    private void writeObject(ObjectOutputStream oos) throws IOException {}

    private void readObject(ObjectInputStream ois)
     throws ClassNotFoundException, IOException {}
}
