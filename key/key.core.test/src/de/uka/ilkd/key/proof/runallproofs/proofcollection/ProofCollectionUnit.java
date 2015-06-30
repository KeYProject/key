package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.IOException;
import java.io.Serializable;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestUnit;

/**
 * Parser {@link ProofCollectionParser} splits a file into several
 * {@link ProofCollectionUnit}s during parsing. The created
 * {@link ProofCollectionUnit}s are combined into a {@link ProofCollection} by
 * the parser. See implementations {@link GroupedProofCollectionUnit} and
 * {@link SingletonProofCollectionUnit} for further details.
 * 
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public abstract class ProofCollectionUnit implements Serializable {

   /**
    * 
    * Creates a {@link RunAllProofsTestUnit} from this
    * {@link ProofCollectionUnit}.
    * 
    * @param parentSettings
    *           Settings used during execution of returned
    *           {@link RunAllProofsTestUnit}.
    */
   public abstract RunAllProofsTestUnit createRunAllProofsTestUnit(
         String testName) throws IOException;

   /**
    * Name of a {@link ProofCollectionUnit}, which is used as prefix for name of
    * {@link RunAllProofsTestUnit} that can be created with method
    * {@link #retrieveTestMethod(ProofCollectionSettings, String)}.
    * 
    * @return Name of this {@link ProofCollectionUnit}.
    */
   abstract String getName() throws IOException;

}
