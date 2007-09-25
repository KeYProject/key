

package java.lang;

import java.io.File;
import java.io.InputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Properties;
import java.util.Set;
import java.util.StringTokenizer;
public class Runtime {
    static SecurityManager securityManager;
    static Properties defaultProperties = new Properties();
    static {}
    private Runtime() {}
    public static Runtime getRuntime() {}
    public void exit(int status) {}
    boolean runShutdownHooks() {}
    public void addShutdownHook(Thread hook) {}
    public boolean removeShutdownHook(Thread hook) {}
    public void halt(int status) {}
    public static void runFinalizersOnExit(boolean finalizeOnExit) {}
    public Process exec(String cmdline) throws IOException {}
    public Process exec(String cmdline, String[] env) throws IOException {}
    public Process exec(String cmdline, String[] env, File dir)
     throws IOException {}
    public Process exec(String[] cmd) throws IOException {}
    public Process exec(String[] cmd, String[] env) throws IOException {}
    public Process exec(String[] cmd, String[] env, File dir)
     throws IOException {}
    public int availableProcessors() {}
    public long freeMemory() {}
    public long totalMemory() {}
    public long maxMemory() {}
    public void gc() {}
    public void runFinalization() {}
    public void traceInstructions(boolean on) {}
    public void traceMethodCalls(boolean on) {}
    public void load(String filename) {}
    private static int loadLib(String filename) {}
    public void loadLibrary(String libname) {}
    public InputStream getLocalizedInputStream(InputStream in) {}
    public OutputStream getLocalizedOutputStream(OutputStream out) {}
}
