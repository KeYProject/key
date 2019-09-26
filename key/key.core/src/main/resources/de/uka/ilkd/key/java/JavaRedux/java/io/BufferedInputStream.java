package java.io;

public final class BufferedInputStream extends java.io.FilterInputStream {

   /*@ public normal_behavior
     @ assignable \nothing;
     @*/
   public BufferedInputStream(java.io.InputStream param0);

   /*@ public normal_behavior
     @ assignable \nothing;
     @*/
   public int read() throws java.io.IOException;

   /*@ public normal_behavior
     @ assignable \nothing;
     @*/
   public void close() throws java.io.IOException;
}