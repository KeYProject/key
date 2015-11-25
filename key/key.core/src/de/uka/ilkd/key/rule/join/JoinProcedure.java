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

package de.uka.ilkd.key.rule.join;

import java.util.LinkedHashSet;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.join.procedures.JoinIfThenElse;
import de.uka.ilkd.key.rule.join.procedures.JoinIfThenElseAntecedent;
import de.uka.ilkd.key.rule.join.procedures.JoinWeaken;
import de.uka.ilkd.key.rule.join.procedures.JoinWithPredicateAbstractionFactory;
import de.uka.ilkd.key.util.Triple;
import de.uka.ilkd.key.util.joinrule.SymbolicExecutionState;

/**
 * Defines a concrete join procedure, in particular the result of joining two
 * terms for a given location variable in two Symbolic Execution states.
 * <p>
 * 
 * For example, computing the join result for a variable x in one state where x
 * is 42 and another one where x is 17, the result could be the update x := c,
 * where c is constrained to be positive by a formula in the returned
 * constraints set.
 * <p>
 * 
 * New join procedures need to be registered in the list CONCRETE_RULES!
 * 
 * @author Dominic Scheurer
 * 
 * @see JoinIfThenElse
 * @see JoinIfThenElseAntecedent
 * @see JoinWeaken
 * @see JoinWithSignLattice
 */
public abstract class JoinProcedure {

    /** Concrete join procedures. */
    static ImmutableList<JoinProcedure> CONCRETE_RULES = ImmutableSLList
            .<JoinProcedure> nil();

    static {
        CONCRETE_RULES =
                ImmutableSLList.<JoinProcedure> nil()
                        .prepend(JoinWeaken.instance())
                        .prepend(JoinWithPredicateAbstractionFactory.instance())
                        .prepend(JoinIfThenElseAntecedent.instance())
                        .prepend(JoinIfThenElse.instance());
    }

    /**
     * Joins two values valueInState1 and valueInState2 of corresponding SE
     * states state1 and state2 to a new value of a join state.
     * 
     * @param v
     *            The variable for which the values should be joined
     * @param state1
     *            First SE state.
     * @param valueInState1
     *            Value in state1.
     * @param state2
     *            Second SE state.
     * @param valueInState2
     *            Value in state2.
     * @param distinguishingFormula
     *            The user-specified distinguishing formula. May be null (for
     *            automatic generation).
     * @param services
     *            The services object.
     * @return A joined value for valueInState1 and valueInState2, that is a
     *         triple consisting of new constraints, the actual value and new
     *         names introduced.
     */
    public abstract Triple<ImmutableSet<Term>, Term, LinkedHashSet<Name>> joinValuesInStates(
            Term v, SymbolicExecutionState state1, Term valueInState1,
            SymbolicExecutionState state2, Term valueInState2,
            Term distinguishingFormula, Services services);

    /**
     * Similar to {@link AbstractBuiltInRuleApp#complete()}. Method was
     * introduced for predicate abstraction (which is not complete if the
     * abstraction predicates are not set).
     *
     * @return true iff the join procedure is complete (all neede parameters are
     *         set).
     */
    public abstract boolean complete();

    /**
     * @return true iff the join procedure requires distinguishable path
     *         conditions. This is usually the case for procedures working with
     *         concrete values of input states, and can be false for abstraction
     *         methods.
     */
    public abstract boolean requiresDistinguishablePathConditions();

    /**
     * Returns the join procedure for the given name.
     *
     * @param procName
     *            Name of the join procedure.
     * @return The join procedure of the given name; null if there is no such
     *         procedure.
     */
    public static JoinProcedure getProcedureByName(String procName) {
        for (JoinProcedure proc : CONCRETE_RULES) {
            if (proc.toString().equals(procName)) {
                return proc;
            }
        }

        return null;
    }

    /**
     * Returns all registered join procedures.
     *
     * @return
     */
    public static ImmutableList<JoinProcedure> getJoinProcedures() {
        return CONCRETE_RULES;
    }

}
