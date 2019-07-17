package org.bouncycastle.openpgp;

/**
 * @generated
 */
public class PGPCompressedDataGenerator extends java.lang.Object implements org.bouncycastle.bcpg.CompressionAlgorithmTags, org.bouncycastle.openpgp.StreamGenerator {
   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public PGPCompressedDataGenerator(int param0);

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public java.io.OutputStream open(java.io.OutputStream param0, byte[] param1) throws java.io.IOException, org.bouncycastle.openpgp.PGPException;

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