package org.apache.commons.csv;

public final class CSVPrinter extends java.lang.Object implements java.io.Flushable, java.io.Closeable {
    
    /*@ public normal_behavior
      @ assignable \nothing;
      @*/
   public void close(boolean param0) throws java.io.IOException;

   /*@ public normal_behavior
      @ assignable \nothing;
     @*/
   public java.lang.Appendable getOut();

   /*@ public normal_behavior
      @ assignable \nothing;
     @*/
   public void printRecord(java.lang.Iterable param0) throws java.io.IOException;
}