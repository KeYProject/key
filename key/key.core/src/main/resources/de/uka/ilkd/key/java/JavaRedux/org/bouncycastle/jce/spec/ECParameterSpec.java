package org.bouncycastle.jce.spec;

public final class ECParameterSpec extends java.lang.Object implements java.security.spec.AlgorithmParameterSpec {
   
   public final org.bouncycastle.math.ec.ECPoint generator;

   //@ public instance invariant \invariant_for(generator);
	
   /*@ public normal_behavior
     @ requires true;
     @ ensures \result == generator;
     @ assignable \strictly_nothing;
     @ determines \result.value \by generator.value;
     @*/
   public org.bouncycastle.math.ec.ECPoint getG();
}