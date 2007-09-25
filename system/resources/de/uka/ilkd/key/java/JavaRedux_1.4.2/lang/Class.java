

package java.lang;

import java.io.InputStream;
import java.io.Serializable;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Member;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.net.URL;
import java.security.AllPermission;
import java.security.Permissions;
import java.security.ProtectionDomain;
import java.security.AccessController;
import java.security.PrivilegedAction;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
public final class Class implements Serializable {
    private static final class StaticData {
        final static ProtectionDomain unknownProtectionDomain;

        static {}
    }

    transient final Object vmdata;
    Class(Object vmdata) {}

    Class(Object vmdata, ProtectionDomain pd) {}
    public static Class forName(String name) throws ClassNotFoundException {}
    public static Class forName(String name, boolean initialize,
                              ClassLoader classloader)
     throws ClassNotFoundException {}
    public Class[] getClasses() {}
    private Class[] internalGetClasses() {}
    public ClassLoader getClassLoader() {}
    public Class getComponentType() {}
    public Constructor getConstructor(Class[] types) throws NoSuchMethodException {}
    public Constructor[] getConstructors() {}
    public Constructor getDeclaredConstructor(Class[] types)
     throws NoSuchMethodException {}
    public Class[] getDeclaredClasses() {}

    Class[] getDeclaredClasses(boolean publicOnly) {}
    public Constructor[] getDeclaredConstructors() {}

    Constructor[] getDeclaredConstructors(boolean publicOnly) {}
    public Field getDeclaredField(String name) throws NoSuchFieldException {}
    public Field[] getDeclaredFields() {}

    Field[] getDeclaredFields(boolean publicOnly) {}
    public Method getDeclaredMethod(String methodName, Class[] types)
     throws NoSuchMethodException {}
    public Method[] getDeclaredMethods() {}

    Method[] getDeclaredMethods(boolean publicOnly) {}
    public Class getDeclaringClass() {}
    public Field getField(String fieldName)
     throws NoSuchFieldException {}
    public Field[] getFields() {}
    private Field[] internalGetFields() {}
    public Package getPackage() {}
    public Class[] getInterfaces() {}

    private static final class MethodKey {

        MethodKey(Method m) {}

        public boolean equals(Object o) {}

        public int hashCode() {}
    }
    public Method getMethod(String methodName, Class[] types)
     throws NoSuchMethodException {}
    private Method internalGetMethod(String methodName, Class[] args) {}
    private static Method matchMethod(Method[] list, String name, Class[] args) {}
    private static boolean matchParameters(Class[] types1, Class[] types2) {}
    public Method[] getMethods() {}
    private Method[] internalGetMethods() {}
    public int getModifiers() {}
    public String getName() {}
    public URL getResource(String resourceName) {}
    public InputStream getResourceAsStream(String resourceName) {}

    private String resourcePath(String resourceName) {}
    public Object[] getSigners() {}
    void setSigners(Object[] signers) {}
    public Class getSuperclass() {}
    public boolean isArray() {}
    public boolean isAssignableFrom(Class c) {}
    public boolean isInstance(Object o) {}
    public boolean isInterface() {}
    public boolean isPrimitive() {}
    public Object newInstance()
     throws InstantiationException, IllegalAccessException {}
    public ProtectionDomain getProtectionDomain() {}
    public String toString() {}
    public boolean desiredAssertionStatus() {}
    private Field internalGetField(String name) {}
    private static String getPackagePortion(String name) {}
    private void memberAccessCheck(int which) {}
}
