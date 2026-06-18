/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.merge;

import java.util.LinkedHashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.merge.procedures.MergeByIfThenElse;
import de.uka.ilkd.key.rule.merge.procedures.MergeIfThenElseAntecedent;
import de.uka.ilkd.key.rule.merge.procedures.MergeTotalWeakening;
import de.uka.ilkd.key.rule.merge.procedures.MergeWithPredicateAbstractionFactory;
import de.uka.ilkd.key.util.mergerule.SymbolicExecutionState;

import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

/**
 * Defines a concrete merge procedure, in particular the result of merging two terms for a given
 * location variable in two Symbolic Execution states.
 * <p>
 *
 * For example, computing the merge result for a variable x in one state where x is 42 and another
 * one where x is 17, the result could be the update x := c, where c is constrained to be positive
 * by a formula in the returned constraints set.
 * <p>
 *
 * New merge procedures need to be registered in the list CONCRETE_RULES!
 *
 * @author Dominic Scheurer
 *
 * @see MergeByIfThenElse
 * @see MergeIfThenElseAntecedent
 * @see MergeTotalWeakening
 */
public abstract class MergeProcedure {

    /** Concrete merge procedures. */
    static ImmutableList<MergeProcedure> CONCRETE_RULES = ImmutableSLList.nil();

    static {
        CONCRETE_RULES =
            ImmutableSLList.<MergeProcedure>nil().prepend(MergeTotalWeakening.instance())
                    .prepend(MergeWithPredicateAbstractionFactory.instance())
                    .prepend(MergeIfThenElseAntecedent.instance())
                    .prepend(MergeByIfThenElse.instance());
    }

    /**
     * Merges two values valueInState1 and valueInState2 of corresponding SE states state1 and
     * state2 to a new value of a merge state.
     *
     * @param v The variable for which the values should be merged
     * @param state1 First SE state.
     * @param valueInState1 Value in state1.
     * @param state2 Second SE state.
     * @param valueInState2 Value in state2.
     * @param distinguishingFormula The user-specified distinguishing formula. May be null (for
     *        automatic generation).
     * @param services The services object.
     * @return The merge result.
     */
    public abstract ValuesMergeResult mergeValuesInStates(JTerm v, SymbolicExecutionState state1,
            JTerm valueInState1, SymbolicExecutionState state2, JTerm valueInState2,
            JTerm distinguishingFormula, Services services);

    /**
     * Similar to {@link AbstractBuiltInRuleApp#complete()}. Method was introduced for predicate
     * abstraction (which is not complete if the abstraction predicates are not set).
     *
     * @return true iff the merge procedure is complete (all neede parameters are set).
     */
    public abstract boolean complete();

    /**
     * @return true iff the merge procedure requires distinguishable path conditions. This is
     *         usually the case for procedures working with concrete values of input states, and can
     *         be false for abstraction methods.
     */
    public abstract boolean requiresDistinguishablePathConditions();

    /**
     * Returns the merge procedure for the given name.
     *
     * @param procName Name of the merge procedure.
     * @return The merge procedure of the given name; null if there is no such procedure.
     */
    public static MergeProcedure getProcedureByName(String procName) {
        for (MergeProcedure proc : CONCRETE_RULES) {
            if (proc.toString().equals(procName)) {
                return proc;
            }
        }

        return null;
    }

    /**
     * Returns all registered merge procedures.
     *
     * @return
     */
    public static ImmutableList<MergeProcedure> getMergeProcedures() {
        return CONCRETE_RULES;
    }

    /**
     * Encapsulates the result of a merge of values.
     *
     * @author Dominic Scheurer
     */
    public record ValuesMergeResult(ImmutableSet<JTerm> newConstraints, JTerm mergeVal,
            LinkedHashSet<Name> newNames,
            LinkedHashSet<JTerm> sideConditions) {
    }

}
