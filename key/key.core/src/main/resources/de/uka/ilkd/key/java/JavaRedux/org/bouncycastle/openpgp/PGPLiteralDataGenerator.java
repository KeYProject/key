package org.bouncycastle.openpgp;

/**
 * @generated
 */
public class PGPLiteralDataGenerator extends java.lang.Object implements org.bouncycastle.openpgp.StreamGenerator {
   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public PGPLiteralDataGenerator();

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public java.io.OutputStream open(java.io.OutputStream param0, char param1, java.lang.String param2, java.util.Date param3, byte[] param4) throws java.io.IOException;

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public void close() throws java.io.IOException;
}