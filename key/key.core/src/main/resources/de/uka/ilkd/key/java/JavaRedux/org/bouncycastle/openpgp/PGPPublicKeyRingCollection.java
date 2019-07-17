package org.bouncycastle.openpgp;

/**
 * @generated
 */
public class PGPPublicKeyRingCollection extends java.lang.Object implements org.bouncycastle.util.Iterable {
   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public PGPPublicKeyRingCollection(java.io.InputStream param0, org.bouncycastle.openpgp.operator.KeyFingerPrintCalculator param1) throws java.io.IOException, org.bouncycastle.openpgp.PGPException;

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public java.util.Iterator getKeyRings();
}