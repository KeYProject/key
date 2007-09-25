


package java.io;

import gnu.classpath.Configuration;
import gnu.java.io.ObjectIdentityWrapper;

import java.lang.reflect.Array;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.Proxy;
import java.util.Arrays;
import java.util.Hashtable;
import java.util.Vector;


public class ObjectInputStream extends InputStream
  implements ObjectInput, ObjectStreamConstants {
    public ObjectInputStream(InputStream in) throws IOException, StreamCorruptedException {}
    public final Object readObject() throws ClassNotFoundException, IOException {}
    private void checkTypeConsistency(String name, ObjectStreamField[] fields1, ObjectStreamField[] fields2)
     throws InvalidClassException {}
    protected ObjectStreamClass readClassDescriptor()
     throws ClassNotFoundException, IOException {}
    public void defaultReadObject()
     throws ClassNotFoundException, IOException, NotActiveException {}
    public void registerValidation(ObjectInputValidation validator,
                                 int priority)
     throws InvalidObjectException, NotActiveException {}
    protected Class resolveClass(ObjectStreamClass osc)
     throws ClassNotFoundException, IOException {}
    private ClassLoader currentLoader() {}
    private ObjectStreamClass lookupClass(Class clazz) {}
    private ObjectStreamClass[] inputGetObjectStreamClasses(Class clazz) {}
    protected Object resolveObject(Object obj) throws IOException {}


    protected Class resolveProxyClass(String[] intfs)
     throws IOException, ClassNotFoundException {}
    protected boolean enableResolveObject(boolean enable)
     throws SecurityException {}
    protected void readStreamHeader()
     throws IOException, StreamCorruptedException {}

    public int read() throws IOException {}

    public int read(byte[] data, int offset, int length) throws IOException {}

    public int available() throws IOException {}

    public void close() throws IOException {}

    public boolean readBoolean() throws IOException {}

    public byte readByte() throws IOException {}

    public int readUnsignedByte() throws IOException {}

    public short readShort() throws IOException {}

    public int readUnsignedShort() throws IOException {}

    public char readChar() throws IOException {}

    public int readInt() throws IOException {}

    public long readLong() throws IOException {}

    public float readFloat() throws IOException {}

    public double readDouble() throws IOException {}

    public void readFully(byte data[]) throws IOException {}

    public void readFully(byte data[], int offset, int size)
     throws IOException {}

    public int skipBytes(int len) throws IOException {}
    public String readLine() throws IOException {}

    public String readUTF() throws IOException {}
    public static abstract class GetField {
        public abstract ObjectStreamClass getObjectStreamClass();

        public abstract boolean defaulted(String name)
         throws IOException, IllegalArgumentException;

        public abstract boolean get(String name, boolean defvalue)
         throws IOException, IllegalArgumentException;

        public abstract char get(String name, char defvalue)
         throws IOException, IllegalArgumentException;

        public abstract byte get(String name, byte defvalue)
         throws IOException, IllegalArgumentException;

        public abstract short get(String name, short defvalue)
         throws IOException, IllegalArgumentException;

        public abstract int get(String name, int defvalue)
         throws IOException, IllegalArgumentException;

        public abstract long get(String name, long defvalue)
         throws IOException, IllegalArgumentException;

        public abstract float get(String name, float defvalue)
         throws IOException, IllegalArgumentException;

        public abstract double get(String name, double defvalue)
         throws IOException, IllegalArgumentException;

        public abstract Object get(String name, Object defvalue)
         throws IOException, IllegalArgumentException;
    }
    public GetField readFields()
     throws IOException, ClassNotFoundException, NotActiveException {}
    protected ObjectInputStream() throws IOException, SecurityException {}
    protected Object readObjectOverride()
     throws ClassNotFoundException, IOException, OptionalDataException {}
    private int assignNewHandle(Object obj) {}

    private Object processResolution(ObjectStreamClass osc, Object obj, int handle)
     throws IOException {}

    private void clearHandles() {}

    private void readNextBlock() throws IOException {}

    private void readNextBlock(byte marker) throws IOException {}

    private void readArrayElements(Object array, Class clazz)
     throws ClassNotFoundException, IOException {}

    private void readFields(Object obj, ObjectStreamClass stream_osc)
     throws ClassNotFoundException, IOException {}
    private boolean setBlockDataMode(boolean on) {}
    private Object newObject(Class real_class, Class constructor_class)
     throws ClassNotFoundException {}
    private void invokeValidators() throws InvalidObjectException {}
    private static native ClassLoader currentClassLoader(SecurityManager sm);

    private void callReadMethod(Method readObject, Class klass, Object obj)
     throws ClassNotFoundException, IOException {}

    private native Object allocateObject(Class clazz)
     throws InstantiationException;

    private native void callConstructor(Class clazz, Object obj);

    private void dumpElement(String msg) {}

    private void dumpElementln(String msg) {}

    static {}
}
class ValidatorAndPriority implements Comparable {
    int priority;
    ObjectInputValidation validator;

    ValidatorAndPriority(ObjectInputValidation validator, int priority) {}

    public int compareTo(Object o) {}
}
