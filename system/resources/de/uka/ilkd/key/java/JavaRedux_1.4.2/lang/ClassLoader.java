


package java.lang;


import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.security.CodeSource;
import java.security.PermissionCollection;
import java.security.Policy;
import java.security.ProtectionDomain;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Map;
public abstract class ClassLoader {
    final Map loadedClasses = new HashMap();
    final Map definedPackages = new HashMap();
    static final ClassLoader systemClassLoader;
    static final ProtectionDomain defaultProtectionDomain;
    static {}
    boolean defaultAssertionStatus;
    static final Map systemPackageAssertionStatus;
    Map packageAssertionStatus;
    static final Map systemClassAssertionStatus;
    Map classAssertionStatus;
    protected ClassLoader() throws SecurityException {}
    protected ClassLoader(ClassLoader parent) {}
    public Class loadClass(String name) throws ClassNotFoundException {}
    protected synchronized Class loadClass(String name, boolean resolve)
     throws ClassNotFoundException {}
    protected Class findClass(String name) throws ClassNotFoundException {}
    protected final Class defineClass(byte[] data, int offset, int len)
     throws ClassFormatError {}
    protected final Class defineClass(String name, byte[] data, int offset,
                                    int len) throws ClassFormatError {}
    protected final synchronized Class defineClass(String name, byte[] data,
                                                 int offset, int len,
                                                 ProtectionDomain domain)
     throws ClassFormatError {}
    protected final void resolveClass(Class c) {}
    protected final Class findSystemClass(String name)
     throws ClassNotFoundException {}
    public final ClassLoader getParent() {}
    protected final void setSigners(Class c, Object[] signers) {}
    protected final synchronized Class findLoadedClass(String name) {}
    public URL getResource(String name) {}
    public final Enumeration getResources(String name) throws IOException {}
    protected Enumeration findResources(String name) throws IOException {}
    protected URL findResource(String name) {}
    public static final URL getSystemResource(String name) {}
    public static Enumeration getSystemResources(String name) throws IOException {}
    public InputStream getResourceAsStream(String name) {}
    public static final InputStream getSystemResourceAsStream(String name) {}
    public static ClassLoader getSystemClassLoader() {}
    protected Package definePackage(String name, String specTitle,
                                  String specVendor, String specVersion,
                                  String implTitle, String implVendor,
                                  String implVersion, URL sealed) {}
    protected Package getPackage(String name) {}
    protected Package[] getPackages() {}
    protected String findLibrary(String name) {}
    public void setDefaultAssertionStatus(boolean enabled) {}
    public synchronized void setPackageAssertionStatus(String name,
                                                     boolean enabled) {}
    public synchronized void setClassAssertionStatus(String name,
                                                   boolean enabled) {}
    public synchronized void clearAssertionStatus() {}
    final boolean isAncestorOf(ClassLoader loader) {}
}
