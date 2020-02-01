package java.nio;

public abstract class ByteBuffer extends java.nio.Buffer implements java.lang.Comparable {
   public static java.nio.ByteBuffer allocate(int param0);
   public final java.nio.ByteBuffer put(byte[] param0);
   public abstract java.nio.ByteBuffer putInt(int param0);
   public final byte[] array();
   public java.nio.ByteBuffer get(byte[] param0, int param1, int param2);
   public static java.nio.ByteBuffer wrap(byte[] param0);
}