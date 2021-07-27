// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.merge.procedures;

import static de.uka.ilkd.key.util.mergerule.MergeRuleUtils.getNewSkolemConstantForPrefix;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.axiom_abstraction.AbstractDomainLattice;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.merge.MergeProcedure;
import de.uka.ilkd.key.util.mergerule.SymbolicExecutionState;

/**
 * Rule that merges two sequents based on a specified set of abstract domain
 * lattices. If no lattice is specified for a given sort, the rule proceeds such
 * that program variables are unchanged if they are equal in both states and
 * applies the if-then-else construction otherwise.
 * 
 * @author Dominic Scheurer
 */
public abstract class MergeWithLatticeAbstraction extends MergeProcedure implements ParametricMergeProcedure {

    /**
     * Returns the abstract domain lattice for the given sort or null if there
     * has no lattice been specified for that sort.
     * 
     * @param s
     *            The sort to return the matching lattice for.
     * @param services
     *            The services object.
     * @return The abstract domain lattice suitable for the given sort. Return
     *         null if there is no abstract domain for that sort; in this case,
     *         an if-then-else merge will be performed.
     */
    protected abstract AbstractDomainLattice getAbstractDomainForSort(Sort s,
            Services services);

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
    public ValuesMergeResult mergeValuesInStates(Term v,
            SymbolicExecutionState state1, Term valueInState1,
            SymbolicExecutionState state2, Term valueInState2,
            Term distinguishingFormula, Services services) {

        final TermBuilder tb = services.getTermBuilder();

        ImmutableSet<Term> newConstraints = DefaultImmutableSet.nil();

        AbstractDomainLattice lattice =
                getAbstractDomainForSort(valueInState1.sort(), services);

        if (lattice != null) {

            AbstractDomainElement mergeElem = null;
            LinkedHashSet<Term> sideConditions = new LinkedHashSet<Term>();

            assert v.op() instanceof ProgramVariable;

            if (getUserChoices().containsKey((ProgramVariable) v.op())) {
                mergeElem = getUserChoices().get((ProgramVariable) v.op());

                sideConditions
                        .add(AbstractDomainLattice.getSideConditionForAxiom(
                                state1, v, mergeElem, services));
                sideConditions
                        .add(AbstractDomainLattice.getSideConditionForAxiom(
                                state2, v, mergeElem, services));
            }
            else {
                // Merge with abstract domain lattice.
                AbstractDomainElement abstrElem1 =
                        lattice.abstractFrom(state1, valueInState1, services);
                AbstractDomainElement abstrElem2 =
                        lattice.abstractFrom(state2, valueInState2, services);

                mergeElem = lattice.join(abstrElem1, abstrElem2);
            }

            Function newSkolemConst =
                    getNewSkolemConstantForPrefix(mergeElem.toString(),
                            valueInState1.sort(), services);
            LinkedHashSet<Name> newNames = new LinkedHashSet<Name>();
            newNames.add(newSkolemConst.name());

            newConstraints =
                    newConstraints.add(mergeElem.getDefiningAxiom(
                            tb.func(newSkolemConst), services));
            
            // NOTE: We also remember the precise values by if-then-else
            // construction. This preserves completeness and should also
            // not be harmful to performance in cases where completeness
            // is also preserved by the lattice. However, if there are
            // lattices where this construction is bad, it may be safely
            // removed (no harm to soundness!).
            /*
            newConstraints =
                    newConstraints.add(tb.equals(tb.func(newSkolemConst),
                            MergeIfThenElse.createIfThenElseTerm(state1, state2,
                                    valueInState1, valueInState2,
                                    distinguishingFormula, services)));
            */
            
            return new ValuesMergeResult(newConstraints,
                    tb.func(newSkolemConst), newNames, sideConditions);

        }
        else {

            return new ValuesMergeResult(DefaultImmutableSet.<Term> nil(),
                    MergeByIfThenElse.createIfThenElseTerm(state1, state2,
                            valueInState1, valueInState2,
                            distinguishingFormula, services),
                    new LinkedHashSet<Name>(), new LinkedHashSet<Term>());

        }

    }

    @Override
    public boolean requiresDistinguishablePathConditions() {
        return false;
    }

}
