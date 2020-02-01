package org.bouncycastle.openpgp;

public class PGPEncryptedDataGenerator extends java.lang.Object implements org.bouncycastle.bcpg.SymmetricKeyAlgorithmTags, org.bouncycastle.openpgp.StreamGenerator {
   public PGPEncryptedDataGenerator(org.bouncycastle.openpgp.operator.PGPDataEncryptorBuilder param0);
   public void addMethod(org.bouncycastle.openpgp.operator.PGPKeyEncryptionMethodGenerator param0);
   public java.io.OutputStream open(java.io.OutputStream param0, byte[] param1) throws java.io.IOException, org.bouncycastle.openpgp.PGPException;
   public void close() throws java.io.IOException;
}