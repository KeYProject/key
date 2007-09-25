


package java.lang;


import java.io.InputStream;
import java.io.PrintStream;
import java.util.Properties;
import java.util.PropertyPermission;
public final class System {
    static {}
    static Properties properties;
    public static final InputStream in;
    public static final PrintStream out;
    public static final PrintStream err;
    private System() {}
    public static void setIn(InputStream in) {}
    public static void setOut(PrintStream out) {}
    public static void setErr(PrintStream err) {}
    public synchronized static void setSecurityManager(SecurityManager sm) {}
    public static SecurityManager getSecurityManager() {}
    public static long currentTimeMillis() {}
    public static void arraycopy(Object src, int srcStart,
                               Object dest, int destStart, int len) {}
    public static int identityHashCode(Object o) {}
    public static Properties getProperties() {}
    public static void setProperties(Properties properties) {}
    public static String getProperty(String key) {}
    public static String getProperty(String key, String def) {}
    public static String setProperty(String key, String value) {}
    public static String getenv(String name) {}
    public static void exit(int status) {}
    public static void gc() {}
    public static void runFinalization() {}
    public static void runFinalizersOnExit(boolean finalizeOnExit) {}
    public static void load(String filename) {}
    public static void loadLibrary(String libname) {}
    public static String mapLibraryName(String libname) {}
}
