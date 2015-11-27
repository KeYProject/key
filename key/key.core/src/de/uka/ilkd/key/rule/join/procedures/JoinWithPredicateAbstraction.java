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

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractPredicateAbstractionLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractionPredicate;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.SimplePredicateAbstractionLattice;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.sort.Sort;

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

    /**
     * The concrete lattice type which determines how abstract elements are
     * generated from abstraction predicates.
     */
    private Class<? extends AbstractPredicateAbstractionLattice> latticeType =
            null;

    /**
     * Default constructor for subclasses.
     */
    protected JoinWithPredicateAbstraction() {
    }

    /**
     * Creates a new instance of {@link JoinWithPredicateAbstraction}. This
     * JoinProcedure cannot be a Singleton since it depends on the given list of
     * predicates!
     *
     * @param predicates
     *            The predicates for the created lattices.
     * @param latticeType
     *            The concrete lattice type which determines how abstract
     *            elements are generated from abstraction predicates.
     */
    public JoinWithPredicateAbstraction(
            Iterable<AbstractionPredicate> predicates,
            Class<? extends AbstractPredicateAbstractionLattice> latticeType) {
        for (AbstractionPredicate pred : predicates) {
            if (!this.predicates.containsKey(pred.getArgSort())) {
                this.predicates.put(pred.getArgSort(),
                        new ArrayList<AbstractionPredicate>());
            }

            this.predicates.get(pred.getArgSort()).add(pred);
        }

        this.latticeType = latticeType;
    }

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
        ArrayList<AbstractionPredicate> applicablePredicates =
                predicates.get(s);

        if (applicablePredicates == null) {
            // A returned null value indicates to
            // JoinWithLatticeAbstraction#joinValuesInStates(...) that the
            // fallback procedure (usually if-then-else join) should be
            // performed instead of a join with lattices
            return null;
        }

        try {
            Constructor<? extends AbstractPredicateAbstractionLattice> latticeConstructor =
                    latticeType.getConstructor(ArrayList.class);

            return latticeConstructor.newInstance(applicablePredicates);
        }
        catch (NoSuchMethodException | SecurityException
                | InstantiationException | IllegalAccessException
                | IllegalArgumentException | InvocationTargetException e) {
            e.printStackTrace();
            return new SimplePredicateAbstractionLattice(applicablePredicates);
        }
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
     * @param predicate
     *            The predicate.
     */
    public void addPredicate(AbstractionPredicate predicate) {
        Sort s = predicate.getArgSort();

        if (!predicates.containsKey(s)) {
            predicates.put(s, new ArrayList<AbstractionPredicate>());
        }

        predicates.get(s).add(predicate);
    }

    /**
     * Adds a new predicate to the set of abstraction predicates.
     * 
     * @param predicates
     *            The predicates to set.
     */
    public void addPredicates(Iterable<AbstractionPredicate> predicates) {
        Iterator<AbstractionPredicate> it = predicates.iterator();
        while (it.hasNext()) {
            addPredicate(it.next());
        }
    }

    /**
     * @return The type of lattice, that is a subclass of
     *         {@link AbstractPredicateAbstractionLattice} which determines how
     *         abstract elements are constructed from abstraction predicates.
     */
    public Class<? extends AbstractPredicateAbstractionLattice> getLatticeType() {
        return latticeType;
    }

    @Override
    public String toString() {
        return DISPLAY_NAME;
    }
}
