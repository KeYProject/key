


package java.io;

import gnu.java.lang.reflect.TypeSignature;

import java.lang.reflect.Field;
import java.security.AccessController;
import java.security.PrivilegedAction;
public class ObjectStreamField implements Comparable {

    ObjectStreamField(Field field) {}
    public ObjectStreamField(String name, Class type) {}
    public ObjectStreamField(String name, Class type, boolean unshared) {}
    ObjectStreamField(String name, String typename) {}
    ObjectStreamField(String name, String typename, ClassLoader loader) {}
    public String getName() {}
    public Class getType() {}
    public char getTypeCode() {}
    public String getTypeString() {}
    public int getOffset() {}
    protected void setOffset(int off) {}
    public boolean isUnshared() {}
    public boolean isPrimitive() {}
    public int compareTo(Object obj) {}
    void setPersistent(boolean persistent) {}
    boolean isPersistent() {}
    void setToSet(boolean toset) {}
    boolean isToSet() {}
    void lookupField(Class clazz) throws NoSuchFieldException, SecurityException {}
    void checkFieldType() throws InvalidClassException {}
    public String toString() {}

    final void setBooleanField(Object obj, boolean val) {}

    final void setByteField(Object obj, byte val) {}

    final void setCharField(Object obj, char val) {}

    final void setShortField(Object obj, short val) {}

    final void setIntField(Object obj, int val) {}

    final void setLongField(Object obj, long val) {}

    final void setFloatField(Object obj, float val) {}

    final void setDoubleField(Object obj, double val) {}

    final void setObjectField(Object obj, Object val) {}
}
