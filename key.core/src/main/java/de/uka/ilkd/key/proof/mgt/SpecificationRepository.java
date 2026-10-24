/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.mgt;

import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.speclang.*;

import org.key_project.util.collection.ImmutableSet;

/**
 * <p>
 * Central storage for all specification elements, such as contracts, class axioms, and loop
 * invariants. Provides methods for adding such elements to the repository, and for retrieving them
 * afterwards.
 * </p>
 *
 * <p>
 * Phase 4 (JMLtk front-end rewrite) is deleting this class slice by slice; all stored state has
 * already moved to {@link Services}-owned components that are shared by
 * {@link Services#copy(boolean)} copies:
 * <ul>
 * <li>statement/loop/block/merge specifications live on the AST nodes
 * ({@code JmlAssert}, {@code SetStatement}, {@code LoopStatement}, {@code StatementBlock},
 * {@code MergePointStatement});</li>
 * <li>the proof↔PO bookkeeping lives in {@code ProofRegistry};</li>
 * <li>class invariants/axioms (and their synthesis) live in {@code ClassAxiomComputer};</li>
 * <li>contracts, initially clauses and their combination/inheritance live in
 * {@code ContractRegistry}.</li>
 * </ul>
 * What remains here is a thin dispatch layer ({@link #addSpecs}, {@link #map}) plus the
 * per-type {@link #processJavaType} hook for profiles (e.g. WD) that post-process a type's
 * specifications.
 * </p>
 */
public class SpecificationRepository {

    protected final Services services;

    public SpecificationRepository(Services services) {
        this.services = services;
    }

    // Thread-safety: all remaining state lives in the Services-owned components this class
    // delegates to (the {@link de.uka.ilkd.key.speclang.ContractRegistry}, guarded by its own
    // monitor, and the {@link de.uka.ilkd.key.speclang.ClassAxiomComputer}, also synchronized);
    // this class itself is stateless and can be called concurrently.

    /**
     * Applies the specified operator to every specification element stored in the
     * {@link Services}-owned components (contracts and initially clauses in the contract
     * registry, invariants and class axioms in the class-axiom computer).
     *
     * @param op an operator.
     * @param services services.
     * @see SpecificationElement#map(UnaryOperator, Services)
     */
    public void map(UnaryOperator<JTerm> op, Services services) {
        services.getContractRegistry().map(op, services);
        services.getClassAxiomComputer().map(op, services);
    }

    /**
     * Registers the passed specification elements, dispatching each to its home:
     * <ul>
     * <li>{@link Contract} → {@link de.uka.ilkd.key.speclang.ContractRegistry#addContract}</li>
     * <li>{@link ClassInvariant} / {@link ClassAxiom} → the
     * {@link de.uka.ilkd.key.speclang.ClassAxiomComputer}</li>
     * <li>{@link InitiallyClause} →
     * {@link de.uka.ilkd.key.speclang.ContractRegistry#addInitiallyClause}</li>
     * <li>loop/block/merge specs → their AST nodes</li>
     * </ul>
     */
    public void addSpecs(ImmutableSet<SpecificationElement> specs) {
        for (SpecificationElement spec : specs) {
            if (spec instanceof Contract) {
                services.getContractRegistry().addContract((Contract) spec);
            } else if (spec instanceof ClassInvariant) {
                services.getClassAxiomComputer().addClassInvariant((ClassInvariant) spec);
            } else if (spec instanceof InitiallyClause) {
                services.getContractRegistry().addInitiallyClause((InitiallyClause) spec);
            } else if (spec instanceof ClassAxiom) {
                services.getClassAxiomComputer().addClassAxiom((ClassAxiom) spec);
            } else if (spec instanceof LoopSpecification loopSpec) {
                loopSpec.getLoop().setLoopInvariant(loopSpec);
            } else if (spec instanceof BlockContract blockContract) {
                blockContract.getBlock().addBlockContract(blockContract);
            } else if (spec instanceof LoopContract loopContract) {
                if (loopContract.isOnBlock()) {
                    loopContract.getBlock().addLoopContract(loopContract);
                } else {
                    loopContract.getLoop().addLoopContract(loopContract);
                }
            } else if (spec instanceof MergeContract mergeContract) {
                mergeContract.getMergePointStatement().addMergeContract(mergeContract);
            } else {
                assert false : "unexpected spec: " + spec + "\n(" + spec.getClass() + ")";
            }
        }
    }

    // region Support SetStatement and JmlAssert
    // JmlAssert/SetStatement specs now live on the AST nodes themselves (JmlSpecCarrier):
    // no repository state is needed here anymore.

    /// Do what ever you want.
    /// Used by WD to modify/add represent clauses.
    public void processJavaType(KeYJavaType kjt) {
    }
    // endregion
}
