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

import java.util.ArrayList;
import java.util.Collections;
import java.util.Map;
import java.util.stream.Collectors;

import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractPredicateAbstractionLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractionPredicate;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.ConjunctivePredicateAbstractionLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.DisjunctivePredicateAbstractionLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.SimplePredicateAbstractionLattice;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.OpReplacer;
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
    private final Map<ProgramVariable, ProgramVariable> atPres;
    private final KeYJavaType kjt;
    private final Class<? extends AbstractPredicateAbstractionLattice> latticeType;
    private final String latticeTypeName;
    private final ArrayList<AbstractionPredicate> abstractionPredicates;

    public PredicateAbstractionMergeContract(MergePointStatement mps,
            Map<ProgramVariable, ProgramVariable> atPres, KeYJavaType kjt,
            String latticeType,
            ArrayList<AbstractionPredicate> abstractionPredicates) {
        this.mps = mps;
        this.atPres = atPres;
        this.kjt = kjt;
        this.latticeType = latticeTypeFromString(latticeType);
        this.latticeTypeName = latticeType;
        this.abstractionPredicates = abstractionPredicates;
    }

    @Override
    public Class<? extends MergeProcedure> getMergeProcedure() {
        return MergeWithPredicateAbstraction.class;
    }

    @Override
    public MergeProcedure getInstantiatedMergeProcedure(Services services) {
        final ArrayList<AbstractionPredicate> abstrPredsWOOldReplacers = abstractionPredicates
                .stream().map(pred -> {
                    Term newPred = pred
                            .getPredicateFormWithPlaceholder().second;
                    for (ProgramVariable var : atPres.keySet()) {
                        newPred = OpReplacer.replace(var, atPres.get(var),
                                newPred, services.getTermFactory());
                    }
                    return AbstractionPredicate.create(newPred,
                            pred.getPredicateFormWithPlaceholder().first,
                            services);
                }).collect(Collectors.toCollection(() -> new ArrayList<>()));
        
        return new MergeWithPredicateAbstraction(abstrPredsWOOldReplacers,
                latticeType, Collections.emptyMap());
    }

    @Override
    public MergePointStatement getMergePointStatement() {
        return mps;
    }

    /**
     * @return A mapping from renamed program variables to the corresponding
     *         values at the beginning of the method execution.
     */
    public Map<ProgramVariable, ProgramVariable> getAtPres() {
        return atPres;
    }

    public Class<? extends AbstractPredicateAbstractionLattice> getLatticeType() {
        return latticeType;
    }

    public String getLatticeTypeName() {
        return latticeTypeName;
    }

    public ArrayList<AbstractionPredicate> getAbstractionPredicates() {
        return abstractionPredicates;
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
