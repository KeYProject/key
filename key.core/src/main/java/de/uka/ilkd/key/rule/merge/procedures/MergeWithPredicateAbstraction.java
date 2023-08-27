/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.merge.procedures;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.*;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.axiom_abstraction.AbstractDomainLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractPredicateAbstractionLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractionPredicate;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.SimplePredicateAbstractionLattice;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.merge.MergeProcedure;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Rule that merges two sequents based on a lattice of user-defined predicates. This procedure is no
 * singleton since the set of predicates has to be defined for each merge application.
 *
 * @author Dominic Scheurer
 */
public class MergeWithPredicateAbstraction extends MergeWithLatticeAbstraction {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(MergeWithPredicateAbstraction.class);

    private static final String DISPLAY_NAME = "MergeByPredicateAbstraction";

    /**
     * Mapping from sorts (e.g., int) to predicates (functions parametric in one argument of the
     * given sort).
     */
    private HashMap<Sort, ArrayList<AbstractionPredicate>> predicates =
        new HashMap<>();

    /**
     * The concrete lattice type which determines how abstract elements are generated from
     * abstraction predicates.
     */
    private Class<? extends AbstractPredicateAbstractionLattice> latticeType = null;

    /**
     * Manually chosen lattice elements for program variables.
     */
    private LinkedHashMap<ProgramVariable, AbstractDomainElement> userChoices = null;

    /**
     * Default constructor for subclasses.
     */
    protected MergeWithPredicateAbstraction() {
    }

    /**
     * Creates a new instance of {@link MergeWithPredicateAbstraction}. This {@link MergeProcedure}
     * cannot be a Singleton since it depends on the given list of predicates!
     *
     * @param predicates The predicates for the created lattices.
     * @param latticeType The concrete lattice type which determines how abstract elements are
     *        generated from abstraction predicates.
     */
    public MergeWithPredicateAbstraction(Iterable<AbstractionPredicate> predicates,
            Class<? extends AbstractPredicateAbstractionLattice> latticeType,
            Map<ProgramVariable, AbstractDomainElement> userChoices) {
        for (AbstractionPredicate pred : predicates) {
            if (!this.predicates.containsKey(pred.getArgSort())) {
                this.predicates.put(pred.getArgSort(), new ArrayList<>());
            }

            this.predicates.get(pred.getArgSort()).add(pred);
        }

        this.latticeType = latticeType;
        this.userChoices = new LinkedHashMap<>();
        this.userChoices.putAll(userChoices);
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.rule.merge.MergeProcedure#complete()
     */
    @Override
    public boolean complete() {
        return predicates != null;
    }

    @Override
    public AbstractDomainLattice getAbstractDomainForSort(final Sort s, final Services services) {
        return instantiateAbstractDomain(s, predicates.get(s), latticeType, services);
    }

    /**
     * Instantiates the abstract domain lattice for the given sort or null if there has no lattice
     * been specified for that sort.
     *
     * @param s {@link Sort} of for elements in the lattice.
     * @param predicates {@link AbstractionPredicate}s for all sorts.
     * @param latticeType Type of {@link AbstractPredicateAbstractionLattice}.
     * @param services The {@link Services} object.
     * @return The corresponding {@link AbstractDomainLattice}.
     */
    public static AbstractDomainLattice instantiateAbstractDomain(final Sort s,
            final List<AbstractionPredicate> applicablePredicates,
            Class<? extends AbstractPredicateAbstractionLattice> latticeType,
            final Services services) {

        if (applicablePredicates == null) {
            // A returned null value indicates to
            // MergeWithLatticeAbstraction#mergeValuesInStates(...) that the
            // fallback procedure (usually if-then-else merge) should be
            // performed instead of a merge with lattices
            return null;
        }

        try {
            Constructor<? extends AbstractPredicateAbstractionLattice> latticeConstructor =
                latticeType.getConstructor(List.class);

            return latticeConstructor.newInstance(applicablePredicates);
        } catch (NoSuchMethodException | SecurityException | InstantiationException
                | IllegalAccessException | IllegalArgumentException | InvocationTargetException e) {
            LOGGER.warn("Failed to instantiate", e);
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
     * @param predicates The abstraction predicates (map from program variables to formula terms).
     */
    public void setPredicates(HashMap<Sort, ArrayList<AbstractionPredicate>> predicates) {
        this.predicates = predicates;
    }

    /**
     * Adds a new predicate to the set of abstraction predicates.
     *
     * @param predicate The predicate.
     */
    public void addPredicate(AbstractionPredicate predicate) {
        Sort s = predicate.getArgSort();

        if (!predicates.containsKey(s)) {
            predicates.put(s, new ArrayList<>());
        }

        predicates.get(s).add(predicate);
    }

    /**
     * Adds a new predicate to the set of abstraction predicates.
     *
     * @param predicates The predicates to set.
     */
    public void addPredicates(Iterable<AbstractionPredicate> predicates) {
        for (AbstractionPredicate predicate : predicates) {
            addPredicate(predicate);
        }
    }

    /**
     * @return The type of lattice, that is a subclass of
     *         {@link AbstractPredicateAbstractionLattice} which determines how abstract elements
     *         are constructed from abstraction predicates.
     */
    public Class<? extends AbstractPredicateAbstractionLattice> getLatticeType() {
        return latticeType;
    }

    /**
     * @return Manually chosen lattice elements for program variables.
     */
    public LinkedHashMap<ProgramVariable, AbstractDomainElement> getUserChoices() {
        return userChoices;
    }

    @Override
    public String toString() {
        return DISPLAY_NAME;
    }
}
