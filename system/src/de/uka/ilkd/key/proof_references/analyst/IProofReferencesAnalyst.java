package de.uka.ilkd.key.proof_references.analyst;

import java.util.LinkedHashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof_references.ProofReferenceUtil;
import de.uka.ilkd.key.proof_references.reference.IProofReference;

/**
 * <p>
 * Instances of this class are used to compute {@link IProofReference} for
 * a given {@link Node} based on the applied rule. Each instance of this class
 * has the knowledge to extract the references for a single rule or a group of similar rules.
 * </p>
 * <p>
 * The complete extraction is done via static methods of {@link ProofReferenceUtil}.
 * </p>
 * @author Martin Hentschel
 * @see ProofReferenceUtil
 * @see IProofReference
 */
public interface IProofReferencesAnalyst {
   /**
    * Computes the {@link IProofReference} for the given {@link Node} which
    * can be {@code null} or an empty set if the applied rule is not supported by this {@link IProofReferencesAnalyst}.
    * @param node The {@link Node} to compute its {@link IProofReference}s.
    * @param services The {@link Services} to use.
    * @return The found {@link IProofReference} or {@code null}/empty set if the applied rule is not supported.
    */
   public LinkedHashSet<IProofReference<?>> computeReferences(Node node, Services services);
}
