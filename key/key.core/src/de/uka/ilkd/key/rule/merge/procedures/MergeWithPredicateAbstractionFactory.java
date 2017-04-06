// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.merge.procedures;

import java.util.LinkedHashMap;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractPredicateAbstractionLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractionPredicate;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.merge.MergeProcedure;
import de.uka.ilkd.key.util.mergerule.SymbolicExecutionState;

/**
 * A factory class for {@link MergeWithPredicateAbstraction} which is itself a
 * {@link MergeProcedure}. This class is used by the merge rule completion GUI
 * which needs in instance for every merge procedure (
 * {@link MergeWithPredicateAbstraction} cannot be statically instantiated since
 * it depends on the list of predicates).
 * {@link MergeWithPredicateAbstractionFactory} is a Singleton.
 *
 * @author Dominic Scheurer
 */
public class MergeWithPredicateAbstractionFactory extends
        MergeWithPredicateAbstraction {

    private static final MergeWithPredicateAbstractionFactory INSTANCE =
            new MergeWithPredicateAbstractionFactory();

    /**
     * Hidden constructor since this class is a Singleton.
     */
    private MergeWithPredicateAbstractionFactory() {
    }

    /**
     * @return The Singleton instance of
     *         {@link MergeWithPredicateAbstractionFactory}.
     */
    public static MergeWithPredicateAbstractionFactory instance() {
        return INSTANCE;
    }
    
    @Override
    public ValuesMergeResult mergeValuesInStates(
            Term v, SymbolicExecutionState state1, Term valueInState1,
            SymbolicExecutionState state2, Term valueInState2,
            Term distinguishingFormula, Services services) {
        throw new UnsupportedOperationException(
                "You need to create an instance of MergeWithPredicateAbstraction.");
    }

    @Override
    public boolean complete() {
        return false;
    }

    /**
     * Creates a complete instance of {@link MergeWithPredicateAbstraction}.
     *
     * @param predicates
     *            The predicates for the lattices to create.
     * @param latticeType
     *            The concrete lattice type which determines how abstract
     *            elements are generated from abstraction predicates.
     * @return A complete instance of {@link MergeWithPredicateAbstraction}.
     */
    public MergeWithPredicateAbstraction instantiate(
            Iterable<AbstractionPredicate> predicates,
            Class<? extends AbstractPredicateAbstractionLattice> latticeType,
            LinkedHashMap<ProgramVariable, AbstractDomainElement> userChoices) {
        return new MergeWithPredicateAbstraction(predicates, latticeType, userChoices);
    }

    @Override
    public String toString() {
        return "MergeByPredicateAbstraction";
    }

}
