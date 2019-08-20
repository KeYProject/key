package org.bouncycastle.jce;

public class ECNamedCurveTable {

   /*@ public normal_behavior
     @ ensures \invariant_for(\result);
     @ assignable \strictly_nothing;
     @*/
   public static org.bouncycastle.jce.spec.ECNamedCurveParameterSpec getParameterSpec(java.lang.String param0);
}