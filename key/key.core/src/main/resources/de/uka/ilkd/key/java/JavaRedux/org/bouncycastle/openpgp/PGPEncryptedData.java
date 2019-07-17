package org.bouncycastle.openpgp;

/**
 * @generated
 */
public abstract class PGPEncryptedData extends java.lang.Object implements org.bouncycastle.bcpg.SymmetricKeyAlgorithmTags {
   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public boolean isIntegrityProtected();

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public boolean verify() throws org.bouncycastle.openpgp.PGPException, java.io.IOException;
}