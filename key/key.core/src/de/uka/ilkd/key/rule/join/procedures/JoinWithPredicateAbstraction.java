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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;

import org.key_project.util.bitops.ImmutableFixedLengthBitSet;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.NotUniqueException;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.axiom_abstraction.AbstractDomainLattice;
import de.uka.ilkd.key.axiom_abstraction.AbstractionPredicate;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;

/**
 * Rule that joins two sequents based on a lattice of user-defined predicates.
 * This procedure is no singleton since the set of predicates has to be defined
 * for each join application.
 * 
 * @author Dominic Scheurer
 */
public class JoinWithPredicateAbstraction extends JoinWithLatticeAbstraction {

    private static final String DISPLAY_NAME = "JoinByPredicateAbstraction";

    /**
     * Mapping from sorts (e.g., int) to predicates (functions parametric in one
     * argument of the given sort).
     */
    private HashMap<Sort, ArrayList<AbstractionPredicate>> predicates =
            new HashMap<Sort, ArrayList<AbstractionPredicate>>();

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.key.rule.join.JoinProcedure#complete()
     */
    @Override
    public boolean complete() {
        return predicates != null;
    }

    @Override
    protected AbstractDomainLattice getAbstractDomainForSort(final Sort s,
            final Services services) {
        // Construct a lattice for all predicates accepting the given sort.
        // This lattice consists of 2^n elements, where n is the number
        // of applicable predicates.
        // The iterator for this lattice will first return the bottom
        // element, then all conjunctions of length n of the predicates,
        // then all conjunctions of length n-1, and so on, until finally
        // the top element is returned.

        ArrayList<AbstractionPredicate> applicablePredicates =
                predicates.get(s);
        int numApplPreds = applicablePredicates.size();

        // We work with bit sets of length n (where n is the number of
        // predicates). Each bit represents a predicate; when the bit is
        // set to 1, the respective predicate should occur in the conjunction.

        final ArrayList<ArrayList<ImmutableFixedLengthBitSet>> bitSetsByNumZeroes =
                new ArrayList<ArrayList<ImmutableFixedLengthBitSet>>();

        // Initialize the list.
        for (int i = 0; i < numApplPreds + 1; i++) {
            bitSetsByNumZeroes.add(new ArrayList<ImmutableFixedLengthBitSet>());
        }

        // bitSet initially represents the number 0.
        ImmutableFixedLengthBitSet bitSet =
                new ImmutableFixedLengthBitSet(numApplPreds);

        for (int i = 0; i < JoinRuleUtils.intPow(2, numApplPreds); i++) {
            int numZeroes = bitSet.getNumOfZeroBits();
            bitSetsByNumZeroes.get(numZeroes).add(bitSet);
            bitSet = bitSet.inc();
        }

        AbstractDomainLattice result = new AbstractDomainLattice() {
            private int nrZeroes = 0;
            private int idx = 0;

            @Override
            public Iterator<AbstractDomainElement> iterator() {
                // TODO Auto-generated method stub
                return null;
            }

            @Override
            public AbstractDomainElement join(AbstractDomainElement a,
                    AbstractDomainElement b) {
                // TODO Auto-generated method stub
                return null;
            }

            private AbstractDomainElement elemFromPredicates(
                    final ImmutableSet<AbstractionPredicate> predicates) {
                return new AbstractDomainElement() {
                    @Override
                    public Name name() {
                        if (predicates.size() == 0) {
                            return new Name("BOTTOM");
                        }
                        
                        StringBuilder result = new StringBuilder();
                        for (AbstractionPredicate pred : predicates) {
                            result
                                .append(pred.name())
                                .append("&");
                        }
                        result.deleteCharAt(result.length() - 1);
                        
                        return new Name(result.toString());
                    }
                    
                    @Override
                    public Term getDefiningAxiom(Term varOrConst, Services services) {
                        TermBuilder tb = services.getTermBuilder();
                        
                        if (predicates.size() == 0) {
                            return tb.ff();
                        }
                        
                        Term result = null;
                        for (AbstractionPredicate pred : predicates) {
                            Term application = pred.apply(varOrConst);
                            if (result == null) {
                                result = pred.apply(application);
                            } else {
                                result = tb.and(result, application);
                            }
                        }
                        
                        return result;
                    }
                };
            }
        };

        return result;
    }

    /**
     * @return The predicates for the abstraction.
     */
    public HashMap<Sort, ArrayList<AbstractionPredicate>> getPredicates() {
        return predicates;
    }

    /**
     * @param predicates
     *            The abstraction predicates (map from program variables to
     *            formula terms).
     */
    public void setPredicates(
            HashMap<Sort, ArrayList<AbstractionPredicate>> predicates) {
        this.predicates = predicates;
    }

    /**
     * Adds a new predicate to the set of abstraction predicates.
     *
     * @param s
     *            The sort of the input program variable for the predicate.
     * @param predicate
     *            The predicate itself.
     */
    public void addPredicate(Sort s, AbstractionPredicate predicate) {
        if (!predicates.containsKey(s)) {
            predicates.put(s, new ArrayList<AbstractionPredicate>());
        }
        
        predicates.get(s).add(predicate);
    }

    @Override
    public String toString() {
        return DISPLAY_NAME;
    }

    /**
     * Looks up and returns the sort of the given name. May return null.
     *
     * @param name
     *            The name for the sort, e.g. "int".
     * @param services
     *            The services object.
     * @return The sort of the given name (may be null).
     */
    private Sort sortFor(String name, Services services) {
        return (Sort) services.getNamespaces().sorts().lookup(new Name(name));
    }
}
