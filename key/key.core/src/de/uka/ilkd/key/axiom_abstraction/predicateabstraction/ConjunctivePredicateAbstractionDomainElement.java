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
 * conjunction of predicates.
 *
 * @author Dominic Scheurer
 */
public class ConjunctivePredicateAbstractionDomainElement extends
        AbstractPredicateAbstractionDomainElement {

    /**
     * The bottom element of any predicate abstraction lattice.
     */
    public static final ConjunctivePredicateAbstractionDomainElement BOTTOM =
            new ConjunctivePredicateAbstractionDomainElement(false);

    /**
     * The top element of any predicate abstraction lattice.
     */
    public static final ConjunctivePredicateAbstractionDomainElement TOP =
            new ConjunctivePredicateAbstractionDomainElement(true);

    /**
     * Constructs a new {@link ConjunctivePredicateAbstractionDomainElement}
     * from a given list of abstraction predicates.
     */
    public ConjunctivePredicateAbstractionDomainElement(
            final ImmutableSet<AbstractionPredicate> predicates) {
        super(predicates);
    }

    /**
     * Constructs a new {@link ConjunctivePredicateAbstractionDomainElement}
     * that is a top element if isTopElem is set to true; otherwise, it is a
     * bottom element.
     */
    private ConjunctivePredicateAbstractionDomainElement(boolean isTopElem) {
        super(isTopElem);
    }

    @Override
    protected Term combinePredicates(Term preds, Term newPred, Services services) {
        return services.getTermBuilder().and(preds, newPred);
    }

    @Override
    public String getPredicateNameCombinationString() {
        return ConjunctivePredicateAbstractionLattice.PREDICATE_NAME_CONBINATION_STRING;
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        return obj instanceof ConjunctivePredicateAbstractionDomainElement
                && (this != TOP || obj == TOP)
                && (this != BOTTOM || obj == BOTTOM)
                && this.getPredicates().equals(
                        ((ConjunctivePredicateAbstractionDomainElement) obj)
                                .getPredicates());
    }

    @Override
    public int hashCode() {
        return 31 * 1 + getPredicates().hashCode();
    }

}
