package org.bouncycastle.openpgp;

public abstract class PGPEncryptedData extends java.lang.Object implements org.bouncycastle.bcpg.SymmetricKeyAlgorithmTags {
   public boolean isIntegrityProtected();
   public boolean verify() throws org.bouncycastle.openpgp.PGPException, java.io.IOException;
}