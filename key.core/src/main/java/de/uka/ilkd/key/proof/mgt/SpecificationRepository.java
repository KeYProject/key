/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;

/**
 * <p>
 * Phase 4 (JMLtk front-end rewrite) is deleting this class slice by slice; all stored state has
 * already moved to {@link Services}-owned components that are shared by
 * {@link Services#copy(boolean)} copies (contracts → {@code ContractRegistry}, class
 * invariants/axioms → {@code ClassAxiomComputer}, proof↔PO bookkeeping → {@code ProofRegistry},
 * statement/loop/block/merge specs → their AST nodes, initially clauses → {@code JMLSpecFactory}
 * at load time). What remains here is only the per-type {@link #processJavaType} hook for
 * profiles (e.g. WD) that post-process a type's specifications; the class is deleted together
 * with that hook (its WD override moves into {@code ContractRegistryWD}).
 * </p>
 */
public class SpecificationRepository {

    protected final Services services;

    public SpecificationRepository(Services services) {
        this.services = services;
    }

    // Thread-safety: this class is stateless; the former state lives in the Services-owned
    // components (ContractRegistry, ClassAxiomComputer, ProofRegistry) or on the AST nodes.

    /// Do what ever you want.
    /// Used by WD to modify/add represent clauses.
    public void processJavaType(KeYJavaType kjt) {
    }
}
