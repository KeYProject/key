package org.apache.commons.csv;

public final class CSVParser extends java.lang.Object implements java.lang.Iterable, java.io.Closeable {

   /*@ public normal_behavior
     @ assignable \nothing;
     @*/
   public java.util.Map getHeaderMap();

   /*@ public normal_behavior
     @ assignable \strictly_nothing;
     @*/
   public long getCurrentLineNumber();
}