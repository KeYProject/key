package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.Serializable;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestUnit;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.settings.ProofCollectionSettings;

/**
 * Parser {@link ProofCollectionParser} splits a file into several
 * {@link ProofCollectionUnit}s during parsing. The only constraint on objects
 * of this type is that an {@link RunAllProofsTestUnit} can be created from
 * them. See implementations {@link GroupedProofCollectionUnit} and
 * {@link SingletonProofCollectionUnit} for further details.
 * 
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public interface ProofCollectionUnit extends Serializable {
   public abstract RunAllProofsTestUnit createRunAllProofsTestUnit(
         ProofCollectionSettings parentSettings);
}
