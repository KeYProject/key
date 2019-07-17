package org.apache.commons.csv;

/**
 * @generated
 */
public final class CSVPrinter extends java.lang.Object implements java.io.Flushable, java.io.Closeable {
   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public void close(boolean param0) throws java.io.IOException;

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public java.lang.Appendable getOut();

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public void printRecord(java.lang.Iterable param0) throws java.io.IOException;
}