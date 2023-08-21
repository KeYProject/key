/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.*;
import java.util.function.UnaryOperator;
import java.util.stream.Collectors;

import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.*;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.rule.merge.MergeProcedure;
import de.uka.ilkd.key.rule.merge.procedures.MergeWithPredicateAbstraction;

import org.key_project.util.java.MapUtil;

/**
 * A {@link MergeContract} for the {@link MergeWithPredicateAbstraction} {@link MergeProcedure}.
 *
 * @author Dominic Scheurer
 */
public class PredicateAbstractionMergeContract implements MergeContract {

    private final static String NAME = "Predicate Abstraction Merge Contract";

    private final MergePointStatement mps;
    private final Map<LocationVariable, Term> atPres;
    private final KeYJavaType kjt;
    private final Class<? extends AbstractPredicateAbstractionLattice> latticeType;
    private final String latticeTypeName;
    private final List<AbstractionPredicate> abstractionPredicates;

    public PredicateAbstractionMergeContract(MergePointStatement mps,
            Map<LocationVariable, Term> atPres, KeYJavaType kjt, String latticeType,
            List<AbstractionPredicate> abstractionPredicates) {
        this.mps = mps;
        this.atPres = atPres;
        this.kjt = kjt;
        this.latticeType = latticeTypeFromString(latticeType);
        this.latticeTypeName = latticeType;
        this.abstractionPredicates = abstractionPredicates;
    }

    @Override
    public PredicateAbstractionMergeContract map(UnaryOperator<Term> op, Services services) {
        return new PredicateAbstractionMergeContract(mps,
            atPres.entrySet().stream().collect(
                MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue()))),
            kjt, latticeTypeName, abstractionPredicates);
    }

    @Override
    public Class<? extends MergeProcedure> getMergeProcedure() {
        return MergeWithPredicateAbstraction.class;
    }

    @Override
    public MergeProcedure getInstantiatedMergeProcedure(Services services) {
        return new MergeWithPredicateAbstraction(getAbstractionPredicates(atPres, services),
            latticeType, Collections.emptyMap());
    }

    @Override
    public MergePointStatement getMergePointStatement() {
        return mps;
    }

    public Map<LocationVariable, Term> getAtPres() {
        return atPres;
    }

    public Class<? extends AbstractPredicateAbstractionLattice> getLatticeType() {
        return latticeType;
    }

    public String getLatticeTypeName() {
        return latticeTypeName;
    }

    /**
     * TODO
     *
     * @param atPres
     * @param services
     * @return
     */
    public ArrayList<AbstractionPredicate> getAbstractionPredicates(
            Map<LocationVariable, Term> atPres, Services services) {
        final Map<Term, Term> replaceMap = getReplaceMap(atPres, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());

        return abstractionPredicates.stream().map(pred -> {
            final Term newPred = or.replace(pred.getPredicateFormWithPlaceholder().second);
            return AbstractionPredicate.create(newPred,
                pred.getPredicateFormWithPlaceholder().first, services);
        }).collect(Collectors.toCollection(ArrayList::new));
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

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    /**
     * TODO
     *
     * @param atPres
     * @param services
     * @return
     */
    private Map<Term, Term> getReplaceMap(Map<LocationVariable, Term> atPres, Services services) {
        final Map<Term, Term> result = new LinkedHashMap<>();

        if (atPres != null) {
            for (Map.Entry<LocationVariable, Term> en : this.atPres.entrySet()) {
                LocationVariable var = en.getKey();
                Term replace = atPres.get(var);
                Term origReplace = en.getValue();
                if (replace != null && origReplace != null) {
                    assert replace.sort().equals(origReplace.sort());
                    result.put(origReplace, replace);
                }
            }
        }

        return result;
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
                "PredicateAbstractionMergeContract: Unexpected lattice type: " + latticeTypeStr);
        }
    }

}
