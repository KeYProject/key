package org.apache.commons.csv;

public final class CSVParser extends java.lang.Object implements java.lang.Iterable, java.io.Closeable {

   /*@ public normal_behavior
     @ ensures (\forall \bigint i; 0 <= i && i < \result.key_seq.length; ((String)\result.key_seq[i]) != null);
     @ ensures \invariant_for(\result);
     @ assignable \nothing;
     @*/
   public java.util.Map getHeaderMap();

   /*@ public normal_behavior
     @ assignable \strictly_nothing;
     @*/
   public long getCurrentLineNumber();
}