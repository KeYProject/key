package org.bouncycastle.openpgp;

/**
 * @generated
 */
public class PGPObjectFactory extends java.lang.Object implements org.bouncycastle.util.Iterable {
   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public PGPObjectFactory(java.io.InputStream param0, org.bouncycastle.openpgp.operator.KeyFingerPrintCalculator param1);

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public java.lang.Object nextObject() throws java.io.IOException;
}