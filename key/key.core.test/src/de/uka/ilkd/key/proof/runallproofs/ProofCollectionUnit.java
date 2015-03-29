package de.uka.ilkd.key.proof.runallproofs;

import java.io.Serializable;

/**
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public abstract class ProofCollectionUnit implements Serializable {
   public abstract boolean processProofObligations();
}
