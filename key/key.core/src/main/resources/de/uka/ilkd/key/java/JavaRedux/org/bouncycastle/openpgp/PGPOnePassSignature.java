package org.bouncycastle.openpgp;

public class PGPOnePassSignature extends java.lang.Object {
   public void init(org.bouncycastle.openpgp.operator.PGPContentVerifierBuilderProvider param0, org.bouncycastle.openpgp.PGPPublicKey param1) throws org.bouncycastle.openpgp.PGPException;
   public void update(byte[] param0);
   public boolean verify(org.bouncycastle.openpgp.PGPSignature param0) throws org.bouncycastle.openpgp.PGPException;
   public void encode(java.io.OutputStream param0) throws java.io.IOException;
}