package org.bouncycastle.openpgp;

/**
 * @generated
 */
public class PGPPublicKey extends java.lang.Object implements org.bouncycastle.bcpg.PublicKeyAlgorithmTags {
   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public int getAlgorithm();

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public java.util.Iterator getUserIDs();

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public void encode(java.io.OutputStream param0) throws java.io.IOException;

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public boolean isEncryptionKey();
}