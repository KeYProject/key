package org.bouncycastle.math.ec;

public final class ECPoint extends java.lang.Object {

   //@ public final ghost \bigint value;
	
   /*@ public normal_behavior
     @ requires true;
     @ ensures \invariant_for(result);
     @ ensures \fresh(\result) && \fresh(\result.*) && \typeof(\result) == \type(ECPoint);
     @ assignable \nothing;
     @ determines \result \by \nothing \new_objects \result;
     @ determines \result.value \by this.value, param0.value;
     @*/
   public org.bouncycastle.math.ec.ECPoint multiply(java.math.BigInteger param0);

   /*@ public normal_behavior
     @ requires true;
     @ ensures \fresh(\result) && \typeof(\result) == \type(byte[]);
     @ assignable \nothing;
     @ determines \result \by \nothing \new_objects \result;
     @ determines result[*] \by value, param0;
     @*/
   public byte[] getEncoded(boolean param0);
}