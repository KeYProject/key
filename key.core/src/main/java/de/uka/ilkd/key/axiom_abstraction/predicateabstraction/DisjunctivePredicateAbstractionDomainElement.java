/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.axiom_abstraction.predicateabstraction;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;

import org.key_project.util.collection.ImmutableSet;

/**
 * An abstract domain element for a predicate abstraction lattice based on the disjunction of
 * predicates.
 *
 * @author Dominic Scheurer
 */
public class DisjunctivePredicateAbstractionDomainElement
        extends AbstractPredicateAbstractionDomainElement {

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
     * Constructs a new {@link DisjunctivePredicateAbstractionDomainElement} from a given list of
     * abstraction predicates.
     */
    public DisjunctivePredicateAbstractionDomainElement(
            final ImmutableSet<AbstractionPredicate> predicates) {
        super(predicates);
    }

    /**
     * Constructs a new {@link DisjunctivePredicateAbstractionDomainElement} that is a top element
     * if isTopElem is set to true; otherwise, it is a bottom element.
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
                && (this != TOP || obj == TOP) && (this != BOTTOM || obj == BOTTOM)
                && this.getPredicates().equals(
                    ((DisjunctivePredicateAbstractionDomainElement) obj).getPredicates());
    }

    @Override
    public int hashCode() {
        return 31 * 2 + getPredicates().hashCode();
    }

}
