package org.bouncycastle.math.ec;

/**
 * @generated
 */
public abstract class ECPoint extends java.lang.Object {
   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public org.bouncycastle.math.ec.ECPoint multiply(java.math.BigInteger param0);

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public byte[] getEncoded(boolean param0);
}