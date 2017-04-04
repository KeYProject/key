// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractPredicateAbstractionLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.ConjunctivePredicateAbstractionLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.DisjunctivePredicateAbstractionLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.SimplePredicateAbstractionLattice;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.rule.merge.MergeProcedure;
import de.uka.ilkd.key.rule.merge.procedures.MergeWithPredicateAbstraction;

/**
 * A {@link MergeContract} for the {@link MergeWithPredicateAbstraction}
 * {@link MergeProcedure}.
 *
 * @author Dominic Scheurer
 */
public class PredicateAbstractionMergeContract implements MergeContract {

    private final static String NAME = "Predicate Abstraction Merge Contract";

    private final MergePointStatement mps;
    private final KeYJavaType kjt;
    private final Class<? extends AbstractPredicateAbstractionLattice> latticeType;

    public PredicateAbstractionMergeContract(MergePointStatement mps,
            KeYJavaType kjt, String latticeType) {
        this.mps = mps;
        this.kjt = kjt;
        this.latticeType = latticeTypeFromString(latticeType);
    }

    @Override
    public Class<? extends MergeProcedure> getMergeProcedure() {
        return MergeWithPredicateAbstraction.class;
    }

    @Override
    public MergePointStatement getMergePointStatement() {
        return mps;
    }

    @Override
    public String getName() {
        return NAME;
    }

    @Override
    public String getDisplayName() {
        return NAME;
    }

    @Override
    public KeYJavaType getKJT() {
        return kjt;
    }

    public Class<? extends AbstractPredicateAbstractionLattice> getLatticeType() {
        return latticeType;
    }

    private static Class<? extends AbstractPredicateAbstractionLattice> latticeTypeFromString(
            String latticeTypeStr) {
        switch (latticeTypeStr) {
        case "simple":
            return SimplePredicateAbstractionLattice.class;
        case "conjunctive":
            return ConjunctivePredicateAbstractionLattice.class;
        case "disjunctive":
            return DisjunctivePredicateAbstractionLattice.class;
        default:
            throw new RuntimeException(
                    "PredicateAbstractionMergeContract: Unexpected lattice type: "
                            + latticeTypeStr);
        }
    }

}
