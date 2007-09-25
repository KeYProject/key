


package java.io;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Member;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.Proxy;
import java.security.AccessController;
import java.security.DigestOutputStream;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.security.PrivilegedAction;
import java.security.Security;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Hashtable;
import java.util.Vector;
import gnu.java.io.NullOutputStream;
import gnu.java.lang.reflect.TypeSignature;
import gnu.java.security.action.SetAccessibleAction;
import gnu.java.security.provider.Gnu;


public class ObjectStreamClass implements Serializable {
    public static ObjectStreamClass lookup(Class cl) {}
    static ObjectStreamClass lookupForClassObject(Class cl) {}
    public String getName() {}
    public Class forClass() {}
    public long getSerialVersionUID() {}
    public ObjectStreamField[] getFields() {}
    public ObjectStreamField getField(String name) {}
    public String toString() {}
    boolean hasWriteMethod() {}
    boolean isSerializable() {}
    boolean isExternalizable() {}
    ObjectStreamClass getSuper() {}
    static ObjectStreamClass[] getObjectStreamClasses(Class clazz) {}
    int getFlags() {}


    ObjectStreamClass(String name, long uid, byte flags,
                    ObjectStreamField[] fields) {}
    void setClass(Class cl, ObjectStreamClass superClass) throws InvalidClassException {}

    void setSuperclass(ObjectStreamClass osc) {}

    void calculateOffsets() {}

    private Method findMethod(Method[] methods, String name, Class[] params,
                            Class returnType) {}

    private void cacheMethods() {}

    private ObjectStreamClass(Class cl) {}
    private void setFlags(Class cl) {}
    private void setFields(Class cl) {}
    private long getClassUID(Class cl) {}
    private ObjectStreamField[] getSerialPersistentFields(Class clazz)
     throws NoSuchFieldException, IllegalAccessException {}
    Externalizable newInstance() throws InvalidClassException {}

    public static final ObjectStreamField[] NO_FIELDS = { };
    ObjectStreamField[] fields;
    int primFieldSize = -1;
    int objectFieldCount;

    Method readObjectMethod;
    Method readResolveMethod;
    boolean realClassIsSerializable;
    boolean realClassIsExternalizable;
    ObjectStreamField[] fieldMapping;
    Class firstNonSerializableParent;

    boolean isProxyClass = false;
}
class InterfaceComparator implements Comparator {
    public int compare(Object o1, Object o2) {}
}
class MemberComparator implements Comparator {
    public int compare(Object o1, Object o2) {}
}
