package org.bouncycastle.openpgp;

public class PGPCompressedDataGenerator extends java.lang.Object implements org.bouncycastle.bcpg.CompressionAlgorithmTags, org.bouncycastle.openpgp.StreamGenerator {
   public PGPCompressedDataGenerator(int param0);
   public java.io.OutputStream open(java.io.OutputStream param0, byte[] param1) throws java.io.IOException, org.bouncycastle.openpgp.PGPException;
   public void close() throws java.io.IOException;
}