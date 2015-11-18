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
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.PredicateAbstractionLattice;
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
        ArrayList<AbstractionPredicate> applicablePredicates =
                predicates.get(s);

        return new PredicateAbstractionLattice(applicablePredicates);
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
