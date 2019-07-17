package org.bouncycastle.openpgp;

/**
 * @generated
 */
public class PGPSecretKey extends java.lang.Object {
   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public org.bouncycastle.openpgp.PGPPrivateKey extractPrivateKey(org.bouncycastle.openpgp.operator.PBESecretKeyDecryptor param0) throws org.bouncycastle.openpgp.PGPException;

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public org.bouncycastle.openpgp.PGPPublicKey getPublicKey();

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public PGPSecretKey(int param0, org.bouncycastle.openpgp.PGPKeyPair param1, java.lang.String param2, org.bouncycastle.openpgp.operator.PGPDigestCalculator param3, org.bouncycastle.openpgp.PGPSignatureSubpacketVector param4, org.bouncycastle.openpgp.PGPSignatureSubpacketVector param5, org.bouncycastle.openpgp.operator.PGPContentSignerBuilder param6, org.bouncycastle.openpgp.operator.PBESecretKeyEncryptor param7) throws org.bouncycastle.openpgp.PGPException;
}