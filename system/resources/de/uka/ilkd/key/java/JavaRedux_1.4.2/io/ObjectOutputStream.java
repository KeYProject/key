


package java.io;

import java.lang.reflect.Array;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.InvocationTargetException;
import java.security.PrivilegedAction;
import java.security.AccessController;
import java.util.Hashtable;

import gnu.java.io.ObjectIdentityWrapper;
import gnu.java.lang.reflect.TypeSignature;
import gnu.java.security.action.SetAccessibleAction;
import gnu.classpath.Configuration;
public class ObjectOutputStream extends OutputStream
  implements ObjectOutput, ObjectStreamConstants {
    public ObjectOutputStream(OutputStream out) throws IOException {}
    public final void writeObject(Object obj) throws IOException {}

    protected void writeClassDescriptor(ObjectStreamClass osc) throws IOException {}
    public void defaultWriteObject()
     throws IOException, NotActiveException {}


    private void markFieldsWritten() throws IOException {}
    public void reset() throws IOException {}


    private void reset(boolean internal) throws IOException {}
    public void useProtocolVersion(int version) throws IOException {}
    public static void setDefaultProtocolVersion(int version)
     throws IOException {}
    protected void annotateClass(Class cl) throws IOException {}

    protected void annotateProxyClass(Class cl) throws IOException {}
    protected Object replaceObject(Object obj) throws IOException {}
    protected boolean enableReplaceObject(boolean enable)
     throws SecurityException {}
    protected void writeStreamHeader() throws IOException {}
    protected ObjectOutputStream() throws IOException, SecurityException {}
    protected void writeObjectOverride(Object obj) throws NotActiveException,
     IOException {}
    public void write(int data) throws IOException {}
    public void write(byte[] b) throws IOException {}
    public void write(byte[] b, int off, int len) throws IOException {}
    public void flush() throws IOException {}
    protected void drain() throws IOException {}
    public void close() throws IOException {}
    public void writeBoolean(boolean data) throws IOException {}
    public void writeByte(int data) throws IOException {}
    public void writeShort(int data) throws IOException {}
    public void writeChar(int data) throws IOException {}
    public void writeInt(int data) throws IOException {}
    public void writeLong(long data) throws IOException {}
    public void writeFloat(float data) throws IOException {}
    public void writeDouble(double data) throws IOException {}
    public void writeBytes(String data) throws IOException {}
    public void writeChars(String data) throws IOException {}
    public void writeUTF(String data) throws IOException {}
    public static abstract class PutField {
        public abstract void put(String name, boolean value);
        public abstract void put(String name, byte value);
        public abstract void put(String name, char value);
        public abstract void put(String name, double value);
        public abstract void put(String name, float value);
        public abstract void put(String name, int value);
        public abstract void put(String name, long value);
        public abstract void put(String name, short value);
        public abstract void put(String name, Object value);
        public abstract void write(ObjectOutput out) throws IOException;
    }

    public PutField putFields() throws IOException {}


    public void writeFields() throws IOException {}
    private void writeBlockDataHeader(int size) throws IOException {}
    private Integer findHandle(Object obj) {}
    private int assignNewHandle(Object obj) {}
    private void clearHandles() {}
    private void writeArraySizeAndElements(Object array, Class clazz)
     throws IOException {}
    private void writeFields(Object obj, ObjectStreamClass osc)
     throws IOException {}
    private boolean setBlockDataMode(boolean on) throws IOException {}


    private void callWriteMethod(Object obj, ObjectStreamClass osc)
     throws IOException {}

    private boolean getBooleanField(Object obj, Class klass, String field_name)
     throws IOException {}

    private byte getByteField(Object obj, Class klass, String field_name)
     throws IOException {}

    private char getCharField(Object obj, Class klass, String field_name)
     throws IOException {}

    private double getDoubleField(Object obj, Class klass, String field_name)
     throws IOException {}

    private float getFloatField(Object obj, Class klass, String field_name)
     throws IOException {}

    private int getIntField(Object obj, Class klass, String field_name)
     throws IOException {}

    private long getLongField(Object obj, Class klass, String field_name)
     throws IOException {}

    private short getShortField(Object obj, Class klass, String field_name)
     throws IOException {}

    private Object getObjectField(Object obj, Class klass, String field_name,
                                 String type_code) throws IOException {}

    private Field getField(Class klass, String name)
     throws java.io.InvalidClassException {}

    private Method getMethod(Class klass, String name, Class[] args)
     throws java.lang.NoSuchMethodException {}

    private void dumpElementln(String msg) {}

    static {}
}
