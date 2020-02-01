package org.bouncycastle.openpgp;

public class PGPPublicKey extends java.lang.Object implements org.bouncycastle.bcpg.PublicKeyAlgorithmTags {
   public int getAlgorithm();
   public java.util.Iterator getUserIDs();
   public void encode(java.io.OutputStream param0) throws java.io.IOException;

   /*@ public normal_behavior
     @ assignable \nothing;
     @*/
   public boolean isEncryptionKey();
}