


package java.lang;

import java.io.OutputStream;
import java.io.InputStream;
public abstract class Process {
    public Process() {}
    public abstract OutputStream getOutputStream();
    public abstract InputStream getInputStream();
    public abstract InputStream getErrorStream();
    public abstract int waitFor() throws InterruptedException;
    public abstract int exitValue();
    public abstract void destroy();
}
