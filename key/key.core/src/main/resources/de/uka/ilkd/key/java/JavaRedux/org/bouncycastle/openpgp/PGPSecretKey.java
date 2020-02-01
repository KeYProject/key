package org.bouncycastle.openpgp;

public class PGPSecretKey extends java.lang.Object {
   public org.bouncycastle.openpgp.PGPPrivateKey extractPrivateKey(org.bouncycastle.openpgp.operator.PBESecretKeyDecryptor param0) throws org.bouncycastle.openpgp.PGPException;
   public org.bouncycastle.openpgp.PGPPublicKey getPublicKey();
   public PGPSecretKey(int param0, org.bouncycastle.openpgp.PGPKeyPair param1, java.lang.String param2, org.bouncycastle.openpgp.operator.PGPDigestCalculator param3, org.bouncycastle.openpgp.PGPSignatureSubpacketVector param4, org.bouncycastle.openpgp.PGPSignatureSubpacketVector param5, org.bouncycastle.openpgp.operator.PGPContentSignerBuilder param6, org.bouncycastle.openpgp.operator.PBESecretKeyEncryptor param7) throws org.bouncycastle.openpgp.PGPException;
}