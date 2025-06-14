/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.merge.procedures;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.axiom_abstraction.AbstractDomainLattice;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.merge.MergeProcedure;
import de.uka.ilkd.key.util.mergerule.SymbolicExecutionState;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import static de.uka.ilkd.key.util.mergerule.MergeRuleUtils.getNewSkolemConstantForPrefix;

/**
 * Rule that merges two sequents based on a specified set of abstract domain lattices. If no lattice
 * is specified for a given sort, the rule proceeds such that program variables are unchanged if
 * they are equal in both states and applies the if-then-else construction otherwise.
 *
 * @author Dominic Scheurer
 */
public abstract class MergeWithLatticeAbstraction extends MergeProcedure
        implements ParametricMergeProcedure {

    /**
     * Returns the abstract domain lattice for the given sort or null if there has no lattice been
     * specified for that sort.
     *
     * @param s The sort to return the matching lattice for.
     * @param services The services object.
     * @return The abstract domain lattice suitable for the given sort. Return null if there is no
     *         abstract domain for that sort; in this case, an if-then-else merge will be performed.
     */
    protected abstract AbstractDomainLattice getAbstractDomainForSort(Sort s, Services services);

    /**
     * @return Manually chosen lattice elements for program variables.
     */
    public abstract LinkedHashMap<ProgramVariable, AbstractDomainElement> getUserChoices();

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.rule.merge.MergeProcedure#complete()
     */
    @Override
    public boolean complete() {
        return true;
    }

    @Override
    public ValuesMergeResult mergeValuesInStates(JTerm v, SymbolicExecutionState state1,
            JTerm valueInState1, SymbolicExecutionState state2, JTerm valueInState2,
            JTerm distinguishingFormula, Services services) {

        final TermBuilder tb = services.getTermBuilder();

        ImmutableSet<JTerm> newConstraints = DefaultImmutableSet.nil();

        AbstractDomainLattice lattice = getAbstractDomainForSort(valueInState1.sort(), services);

        if (lattice != null) {

            AbstractDomainElement mergeElem;
            LinkedHashSet<JTerm> sideConditions = new LinkedHashSet<>();

            assert v.op() instanceof ProgramVariable;

            if (getUserChoices().containsKey((ProgramVariable) v.op())) {
                mergeElem = getUserChoices().get((ProgramVariable) v.op());

                sideConditions.add(
                    AbstractDomainLattice.getSideConditionForAxiom(state1, v, mergeElem, services));
                sideConditions.add(
                    AbstractDomainLattice.getSideConditionForAxiom(state2, v, mergeElem, services));
            } else {
                // Merge with abstract domain lattice.
                AbstractDomainElement abstrElem1 =
                    lattice.abstractFrom(state1, valueInState1, services);
                AbstractDomainElement abstrElem2 =
                    lattice.abstractFrom(state2, valueInState2, services);

                mergeElem = lattice.join(abstrElem1, abstrElem2);
            }

            Function newSkolemConst =
                getNewSkolemConstantForPrefix(mergeElem.toString(), valueInState1.sort(), services);
            LinkedHashSet<Name> newNames = new LinkedHashSet<>();
            newNames.add(newSkolemConst.name());

            newConstraints =
                newConstraints.add(mergeElem.getDefiningAxiom(tb.func(newSkolemConst), services));

            // NOTE: We also remember the precise values by if-then-else
            // construction. This preserves completeness and should also
            // not be harmful to performance in cases where completeness
            // is also preserved by the lattice. However, if there are
            // lattices where this construction is bad, it may be safely
            // removed (no harm to soundness!).
            /*
             * newConstraints = newConstraints.add(tb.equals(tb.func(newSkolemConst),
             * MergeIfThenElse.createIfThenElseTerm(state1, state2, valueInState1, valueInState2,
             * distinguishingFormula, services)));
             */

            return new ValuesMergeResult(newConstraints, tb.func(newSkolemConst), newNames,
                sideConditions);

        } else {

            return new ValuesMergeResult(DefaultImmutableSet.nil(),
                MergeByIfThenElse.createIfThenElseTerm(state1, state2, valueInState1, valueInState2,
                    distinguishingFormula, services),
                new LinkedHashSet<>(), new LinkedHashSet<>());

        }

    }

    @Override
    public boolean requiresDistinguishablePathConditions() {
        return false;
    }

}
