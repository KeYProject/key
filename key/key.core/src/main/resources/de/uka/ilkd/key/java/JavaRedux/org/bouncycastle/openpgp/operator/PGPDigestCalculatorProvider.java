package org.bouncycastle.openpgp.operator;

public interface PGPDigestCalculatorProvider {
   public abstract org.bouncycastle.openpgp.operator.PGPDigestCalculator get(int param0) throws org.bouncycastle.openpgp.PGPException;
}