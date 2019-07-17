package org.bouncycastle.openpgp;

/**
 * @generated
 */
public class PGPSignatureGenerator extends java.lang.Object {
   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public PGPSignatureGenerator(org.bouncycastle.openpgp.operator.PGPContentSignerBuilder param0);

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public void init(int param0, org.bouncycastle.openpgp.PGPPrivateKey param1) throws org.bouncycastle.openpgp.PGPException;

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public void setHashedSubpackets(org.bouncycastle.openpgp.PGPSignatureSubpacketVector param0);

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public org.bouncycastle.openpgp.PGPOnePassSignature generateOnePassVersion(boolean param0) throws org.bouncycastle.openpgp.PGPException;

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public void update(byte[] param0, int param1, int param2);

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public org.bouncycastle.openpgp.PGPSignature generate() throws org.bouncycastle.openpgp.PGPException;

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public void update(byte param0);
}