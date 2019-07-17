package org.bouncycastle.openpgp.operator;

/**
 * @generated
 */
public interface PGPDigestCalculatorProvider {
   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public abstract org.bouncycastle.openpgp.operator.PGPDigestCalculator get(int param0) throws org.bouncycastle.openpgp.PGPException;
}