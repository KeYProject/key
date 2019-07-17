package org.bouncycastle.openpgp;

/**
 * @generated
 */
public class PGPOnePassSignature extends java.lang.Object {
   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public void init(org.bouncycastle.openpgp.operator.PGPContentVerifierBuilderProvider param0, org.bouncycastle.openpgp.PGPPublicKey param1) throws org.bouncycastle.openpgp.PGPException;

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public void update(byte[] param0);

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public boolean verify(org.bouncycastle.openpgp.PGPSignature param0) throws org.bouncycastle.openpgp.PGPException;

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public void encode(java.io.OutputStream param0) throws java.io.IOException;
}