package de.uka.ilkd.key.proof_references.reference;

import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof_references.ProofReferenceUtil;
import de.uka.ilkd.key.proof_references.analyst.IProofReferencesAnalyst;
import de.uka.ilkd.key.speclang.Contract;

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
    * <p>
    * A method call which determines the possible implementations of a called method.
    * </p>
    * <p>
    * References of this kind should provide an {@link IProgramMethod} as target ({@link #getTarget()}). 
    * </p>
    */
   public static final String CALL_METHOD = "Call Method";
   
   /**
    * <p>
    * The proof step "methodBodyExpand" that inlines methods.
    * </p>
    * <p>
    * References of this kind should provide an {@link IProgramMethod} as target ({@link #getTarget()}). 
    * </p>
    */
   public static final String INLINE_METHOD = "Inline Method";

   /**
    * <p>
    * The proof step "Use Operation Contract" which approximates a method call via its method contract
    * and also the usage of dependency contracts.
    * </p>
    * <p>
    * References of this kind should provide a {@link Contract} as target ({@link #getTarget()}). 
    * </p>
    */
   public static final String USE_CONTRACT = "Use Contract";
   
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
