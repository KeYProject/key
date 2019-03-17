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

package de.uka.ilkd.key.axiom_abstraction.predicateabstraction;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;

/**
 * An abstract domain element for a predicate abstraction lattice based on the
 * disjunction of predicates.
 *
 * @author Dominic Scheurer
 */
public class DisjunctivePredicateAbstractionDomainElement extends
        AbstractPredicateAbstractionDomainElement {

    /**
     * The bottom element of any predicate abstraction lattice.
     */
    public static final DisjunctivePredicateAbstractionDomainElement BOTTOM =
            new DisjunctivePredicateAbstractionDomainElement(false);

    /**
     * The top element of any predicate abstraction lattice.
     */
    public static final DisjunctivePredicateAbstractionDomainElement TOP =
            new DisjunctivePredicateAbstractionDomainElement(true);

    /**
     * Constructs a new {@link DisjunctivePredicateAbstractionDomainElement}
     * from a given list of abstraction predicates.
     */
    public DisjunctivePredicateAbstractionDomainElement(
            final ImmutableSet<AbstractionPredicate> predicates) {
        super(predicates);
    }

    /**
     * Constructs a new {@link DisjunctivePredicateAbstractionDomainElement}
     * that is a top element if isTopElem is set to true; otherwise, it is a
     * bottom element.
     */
    private DisjunctivePredicateAbstractionDomainElement(boolean isTopElem) {
        super(isTopElem);
    }

    @Override
    protected Term combinePredicates(Term preds, Term newPred, Services services) {
        return services.getTermBuilder().or(preds, newPred);
    }

    @Override
    public String getPredicateNameCombinationString() {
        return DisjunctivePredicateAbstractionLattice.PREDICATE_NAME_CONBINATION_STRING;
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        return obj instanceof DisjunctivePredicateAbstractionDomainElement
                && (this != TOP || obj == TOP)
                && (this != BOTTOM || obj == BOTTOM)
                && this.getPredicates().equals(
                        ((DisjunctivePredicateAbstractionDomainElement) obj)
                                .getPredicates());
    }

    @Override
    public int hashCode() {
        return 31 * 2 + getPredicates().hashCode();
    }

}
