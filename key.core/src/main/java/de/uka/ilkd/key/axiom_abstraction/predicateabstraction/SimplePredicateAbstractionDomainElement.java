/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.axiom_abstraction.predicateabstraction;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;

import org.key_project.util.collection.ImmutableSet;

/**
 * An abstract domain element for a predicate abstraction lattice encapsulating exactly one
 * abstraction predicate.
 *
 * @author Dominic Scheurer
 */
public class SimplePredicateAbstractionDomainElement
        extends AbstractPredicateAbstractionDomainElement {

    /**
     * The bottom element of any predicate abstraction lattice.
     */
    public static final SimplePredicateAbstractionDomainElement BOTTOM =
        new SimplePredicateAbstractionDomainElement(false);

    /**
     * The top element of any predicate abstraction lattice.
     */
    public static final SimplePredicateAbstractionDomainElement TOP =
        new SimplePredicateAbstractionDomainElement(true);

    /**
     * Constructs a new {@link SimplePredicateAbstractionDomainElement} from a given list of
     * abstraction predicates.
     */
    public SimplePredicateAbstractionDomainElement(
            final ImmutableSet<AbstractionPredicate> predicates) {
        super(predicates);
    }

    /**
     * Constructs a new {@link SimplePredicateAbstractionDomainElement} that is a top element if
     * isTopElem is set to true; otherwise, it is a bottom element.
     */
    private SimplePredicateAbstractionDomainElement(boolean isTopElem) {
        super(isTopElem);
    }

    @Override
    protected Term combinePredicates(Term preds, Term newPred, Services services) {
        throw new RuntimeException(
            "In the simple predicate abstraction lattice, " + "elements should not be combined.");
    }

    @Override
    public String getPredicateNameCombinationString() {
        return SimplePredicateAbstractionLattice.PREDICATE_NAME_CONBINATION_STRING;
    }

    /*
     * (non-Javadoc)
     *
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        return obj instanceof SimplePredicateAbstractionDomainElement && (this != TOP || obj == TOP)
                && (this != BOTTOM || obj == BOTTOM) && this.getPredicates()
                        .equals(((SimplePredicateAbstractionDomainElement) obj).getPredicates());
    }

    @Override
    public int hashCode() {
        return 31 * 3 + getPredicates().hashCode();
    }

}
