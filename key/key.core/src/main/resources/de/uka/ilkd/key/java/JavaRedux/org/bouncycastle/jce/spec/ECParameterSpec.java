package org.bouncycastle.jce.spec;

public class ECParameterSpec extends java.lang.Object implements java.security.spec.AlgorithmParameterSpec {
   
   public final org.bouncycastle.math.ec.ECPoint generator;
	
   /*@ public normal_behavior
     @ requires true;
     @ ensures \result == generator;
     @ assignable \nothing;
     @ determines \result \by generator;
     @*/
   public org.bouncycastle.math.ec.ECPoint getG();
}