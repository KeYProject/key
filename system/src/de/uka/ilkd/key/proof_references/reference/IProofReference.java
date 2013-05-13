package de.uka.ilkd.key.proof_references.reference;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof_references.ProofReferenceUtil;
import de.uka.ilkd.key.proof_references.analyst.IProofReferencesAnalyst;

/**
 * A proof reference which points to a source member used during proof.
 * By default, instances are created via {@link IProofReferencesAnalyst}s
 * during reference computation via static methods of {@link ProofReferenceUtil}.
 * @author Martin Hentschel
 * @see ProofReferenceUtil
 * @see IProofReferencesAnalyst.
 */
public interface IProofReference<T> {
   /**
    * Returns the reference kind which is a human readable {@link String}.
    * @return The reference kind as human readable {@link String}.
    */
   public String getKind();
   
   /**
    * Returns the {@link Node} in which the reference was found.
    * @return The {@link Node} in which the reference was found.
    */
   public Node getNode();
   
   /**
    * Returns the target source member.
    * @return The target source member.
    */
   public T getTarget();
}
