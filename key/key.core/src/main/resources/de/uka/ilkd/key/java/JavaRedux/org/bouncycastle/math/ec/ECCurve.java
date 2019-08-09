package org.bouncycastle.math.ec;

public abstract class ECCurve extends java.lang.Object {
   
   public final java.math.BigInteger order;
	
   /*@ public normal_behavior
     @ requires true;
     @ ensures \result == order;
     @ assignable \nothing;
     @ determines \result \by order;
     @*/
   public java.math.BigInteger getOrder();

   public static abstract class AbstractFp extends org.bouncycastle.math.ec.ECCurve {
   }
}