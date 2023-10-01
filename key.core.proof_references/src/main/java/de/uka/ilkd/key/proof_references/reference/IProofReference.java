/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof_references.reference;

import java.util.Collection;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof_references.ProofReferenceUtil;
import de.uka.ilkd.key.proof_references.analyst.IProofReferencesAnalyst;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;

/**
 * A proof reference which points to a source member used during proof. By default, instances are
 * created via {@link IProofReferencesAnalyst}s during reference computation via static methods of
 * {@link ProofReferenceUtil}.
 *
 * @author Martin Hentschel
 * @see ProofReferenceUtil
 * @see IProofReferencesAnalyst
 */
public interface IProofReference<T> {
    /**
     * <p>
     * A method call which determines the possible implementations of a called method.
     * </p>
     * <p>
     * References of this kind should provide an {@link IProgramMethod} as target
     * ({@link #getTarget()}).
     * </p>
     */
    String CALL_METHOD = "Call Method";

    /**
     * <p>
     * The proof step "methodBodyExpand" that inlines methods.
     * </p>
     * <p>
     * References of this kind should provide an {@link IProgramMethod} as target
     * ({@link #getTarget()}).
     * </p>
     */
    String INLINE_METHOD = "Inline Method";

    /**
     * <p>
     * The proof step "Use Operation Contract" which approximates a method call via its method
     * contract and also the usage of dependency contracts.
     * </p>
     * <p>
     * References of this kind should provide a {@link Contract} as target ({@link #getTarget()}).
     * </p>
     */
    String USE_CONTRACT = "Use Contract";

    /**
     * <p>
     * Read/Write access of a field like instance or class variables during proof.
     * </p>
     * <p>
     * References of this kind should provide an {@link IProgramVariable} as target
     * ({@link #getTarget()}).
     * </p>
     */
    String ACCESS = "Access";

    /**
     * <p>
     * Used invariants during proof.
     * </p>
     * <p>
     * References of this kind should provide an {@link ClassInvariant} as target
     * ({@link #getTarget()}).
     * </p>
     */
    String USE_INVARIANT = "Use Invariant";

    /**
     * <p>
     * Used axioms during proof.
     * </p>
     * <p>
     * References of this kind should provide an {@link ClassAxiom} as target
     * ({@link #getTarget()}).
     * </p>
     */
    String USE_AXIOM = "Use Axiom";

    /**
     * Returns the reference kind which is a human readable {@link String}.
     *
     * @return The reference kind as human readable {@link String}.
     */
    String getKind();

    /**
     * Returns the {@link Node}s in which the reference was found.
     *
     * @return The {@link Node}s in which the reference was found.
     */
    LinkedHashSet<Node> getNodes();

    /**
     * Adds the given {@link Node}s to the own {@link Node}s.
     *
     * @param nodes The {@link Node}s to add.
     */
    void addNodes(Collection<Node> nodes);

    /**
     * Returns the target source member.
     *
     * @return The target source member.
     */
    T getTarget();

    /**
     * Returns the source {@link Proof}.
     *
     * @return The source {@link Proof}.
     */
    Proof getSource();
}
