


package java.util;

import java.lang.ref.Reference;
import java.lang.ref.SoftReference;
import java.io.InputStream;
import java.io.IOException;
import java.security.AccessController;
import java.security.PrivilegedAction;
public abstract class ResourceBundle {
    protected ResourceBundle parent;
    private static final class Security extends SecurityManager {
        Security() {}
        ClassLoader getCallingClassLoader() {}
    }
    public ResourceBundle() {}
    public final String getString(String key) {}
    public final String[] getStringArray(String key) {}
    public final Object getObject(String key) {}
    public Locale getLocale() {}
    protected void setParent(ResourceBundle parent) {}
    public static final ResourceBundle getBundle(String baseName) {}
    public static final ResourceBundle getBundle(String baseName,
                                               Locale locale) {}
    public static final synchronized ResourceBundle getBundle(String baseName, Locale locale, ClassLoader classLoader) {}
    protected abstract Object handleGetObject(String key);
    public abstract Enumeration getKeys();
    private static final ResourceBundle tryBundle(String localizedName,
                                                Locale locale,
                                                ClassLoader classloader,
                                                ResourceBundle bundle,
                                                HashMap cache) {}
    private static final ResourceBundle tryLocalBundle(String baseName,
                                                     Locale locale,
                                                     ClassLoader classloader,
                                                     ResourceBundle bundle,
                                                     HashMap cache) {}
}
