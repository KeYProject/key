package java.io;

public abstract class OutputStream extends java.lang.Object implements java.io.Closeable, java.io.Flushable {
    
   public void write(byte[] param0, int param1, int param2) throws java.io.IOException;
   public void close() throws java.io.IOException;
}