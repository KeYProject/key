package org.bouncycastle.math.ec;

public abstract class ECCurve extends java.lang.Object {
   
   //@ public final ghost \bigint order;
	
   /*@ public normal_behavior
     @ requires true;
     @ ensures \result.value == order;
     @ assignable \nothing;
     @ determines \result \by \nothing;
     @ determines \result.value \by order;
     @*/
   public java.math.BigInteger getOrder();

   public static abstract class AbstractFp extends org.bouncycastle.math.ec.ECCurve {
   }
}