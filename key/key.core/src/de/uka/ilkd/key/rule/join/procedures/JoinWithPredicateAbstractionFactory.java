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

package de.uka.ilkd.key.rule.join.procedures;

import java.util.LinkedHashMap;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractPredicateAbstractionLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractionPredicate;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.join.JoinProcedure;
import de.uka.ilkd.key.util.joinrule.SymbolicExecutionState;

/**
 * A factory class for {@link JoinWithPredicateAbstraction} which is itself a
 * {@link JoinProcedure}. This class is used by the join rule completion GUI
 * which needs in instance for every join procedure (
 * {@link JoinWithPredicateAbstraction} cannot be statically instantiated since
 * it depends on the list of predicates).
 * {@link JoinWithPredicateAbstractionFactory} is a Singleton.
 *
 * @author Dominic Scheurer
 */
public class JoinWithPredicateAbstractionFactory extends
        JoinWithPredicateAbstraction {

    private static final JoinWithPredicateAbstractionFactory INSTANCE =
            new JoinWithPredicateAbstractionFactory();

    /**
     * Hidden constructor since this class is a Singleton.
     */
    private JoinWithPredicateAbstractionFactory() {
    }

    /**
     * @return The Singleton instance of
     *         {@link JoinWithPredicateAbstractionFactory}.
     */
    public static JoinWithPredicateAbstractionFactory instance() {
        return INSTANCE;
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.key.rule.join.JoinProcedure#joinValuesInStates(de.uka.ilkd
     * .key.logic.Term, de.uka.ilkd.key.util.joinrule.SymbolicExecutionState,
     * de.uka.ilkd.key.logic.Term,
     * de.uka.ilkd.key.util.joinrule.SymbolicExecutionState,
     * de.uka.ilkd.key.logic.Term, de.uka.ilkd.key.logic.Term,
     * de.uka.ilkd.key.java.Services)
     */
    @Override
    public ValuesJoinResult joinValuesInStates(
            Term v, SymbolicExecutionState state1, Term valueInState1,
            SymbolicExecutionState state2, Term valueInState2,
            Term distinguishingFormula, Services services) {
        throw new UnsupportedOperationException(
                "You need to create an instance of JoinWithPredicateAbstraction.");
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.key.rule.join.JoinProcedure#complete()
     */
    @Override
    public boolean complete() {
        return false;
    }

    /**
     * Creates a complete instance of {@link JoinWithPredicateAbstraction}.
     *
     * @param predicates
     *            The predicates for the lattices to create.
     * @param latticeType
     *            The concrete lattice type which determines how abstract
     *            elements are generated from abstraction predicates.
     * @return A complete instance of {@link JoinWithPredicateAbstraction}.
     */
    public JoinWithPredicateAbstraction instantiate(
            Iterable<AbstractionPredicate> predicates,
            Class<? extends AbstractPredicateAbstractionLattice> latticeType,
            LinkedHashMap<ProgramVariable, AbstractDomainElement> userChoices) {
        return new JoinWithPredicateAbstraction(predicates, latticeType, userChoices);
    }

    @Override
    public String toString() {
        return "JoinByPredicateAbstraction";
    }

}
