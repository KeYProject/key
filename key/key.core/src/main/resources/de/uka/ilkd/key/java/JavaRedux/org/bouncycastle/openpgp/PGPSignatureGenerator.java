package org.bouncycastle.openpgp;

public class PGPSignatureGenerator extends java.lang.Object {
   public PGPSignatureGenerator(org.bouncycastle.openpgp.operator.PGPContentSignerBuilder param0);
   public void init(int param0, org.bouncycastle.openpgp.PGPPrivateKey param1) throws org.bouncycastle.openpgp.PGPException;
   public void setHashedSubpackets(org.bouncycastle.openpgp.PGPSignatureSubpacketVector param0);
   public org.bouncycastle.openpgp.PGPOnePassSignature generateOnePassVersion(boolean param0) throws org.bouncycastle.openpgp.PGPException;
   public void update(byte[] param0, int param1, int param2);
   public org.bouncycastle.openpgp.PGPSignature generate() throws org.bouncycastle.openpgp.PGPException;
   public void update(byte param0);
}