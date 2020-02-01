package org.bouncycastle.openpgp;

public class PGPPublicKeyRing extends org.bouncycastle.openpgp.PGPKeyRing implements org.bouncycastle.util.Iterable {

    /*@ public normal_behavior
      @ ensures \result.index == 0;
      @ assignable \nothing;
      @*/
    public java.util.CollectionIterator getPublicKeys();
}