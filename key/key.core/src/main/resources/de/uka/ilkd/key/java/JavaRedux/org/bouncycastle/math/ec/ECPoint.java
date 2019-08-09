package org.bouncycastle.math.ec;

public abstract class ECPoint extends java.lang.Object {
   
   public final int value;
	
   /*@ public normal_behavior
     @ requires true;
     @ ensures true;
     @ assignable \nothing;
     @ determines \result.value \by this.value, param0.value;
     @*/
   public org.bouncycastle.math.ec.ECPoint multiply(java.math.BigInteger param0);

   /*@ public normal_behavior
     @ requires true;
     @ ensures true;
     @ assignable \nothing;
     @ determines \result, result[*] \by value, param0;
     @*/
   public byte[] getEncoded(boolean param0);
}