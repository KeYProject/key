package org.bouncycastle.openpgp;

/**
 * @generated
 */
public class PGPEncryptedDataGenerator extends java.lang.Object implements org.bouncycastle.bcpg.SymmetricKeyAlgorithmTags, org.bouncycastle.openpgp.StreamGenerator {
   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public PGPEncryptedDataGenerator(org.bouncycastle.openpgp.operator.PGPDataEncryptorBuilder param0);

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public void addMethod(org.bouncycastle.openpgp.operator.PGPKeyEncryptionMethodGenerator param0);

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