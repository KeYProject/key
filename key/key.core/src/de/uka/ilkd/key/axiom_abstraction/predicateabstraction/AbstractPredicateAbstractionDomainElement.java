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

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

/**
 * An abstract domain element for a predicate abstraction lattice.
 *
 * @author Dominic Scheurer
 */
public abstract class AbstractPredicateAbstractionDomainElement extends
        AbstractDomainElement {

    private ImmutableSet<AbstractionPredicate> predicates = null;
    private boolean topElem = false;

    /**
     * Constructs a new {@link AbstractPredicateAbstractionDomainElement} from a
     * given list of abstraction predicates.
     */
    public AbstractPredicateAbstractionDomainElement(
            final ImmutableSet<AbstractionPredicate> predicates) {
        this.predicates = predicates;
    }

    /**
     * Constructs a new {@link AbstractPredicateAbstractionDomainElement} that
     * is a top element if isTopElem is set to true; otherwise, it is a bottom
     * element.
     */
    protected AbstractPredicateAbstractionDomainElement(boolean isTopElem) {
        this.predicates = DefaultImmutableSet.<AbstractionPredicate> nil();
        this.topElem = isTopElem;
    }

    /**
     * @return Whether this element is the top element of the lattice (the axiom
     *         of which is true for every input).
     */
    protected boolean isTopElem() {
        return topElem;
    }

    /**
     * @return The abstraction predicates for this domain element.
     */
    public ImmutableSet<AbstractionPredicate> getPredicates() {
        return predicates;
    }

    /**
     * @param predicates
     *            the abstraction predicates for this domain element to set.
     */
    public void setPredicates(ImmutableSet<AbstractionPredicate> predicates) {
        this.predicates = predicates;
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.key.logic.Named#name()
     */
    @Override
    public Name name() {
        if (topElem) {
            return new Name("TOP");
        }

        if (predicates.size() == 0) {
            return new Name("BOTTOM");
        }

        StringBuilder result = new StringBuilder();
        int i = 1;
        for (AbstractionPredicate pred : predicates) {
            result.append(pred.name());

            if (i++ < predicates.size()) {
                result.append(getPredicateNameCombinationString());
            }
        }

        return new Name(result.toString());
    }

    /**
     * @return The String which is used for combining the names of predicates
     *         for lattice types where multiple predicates determine an abstract
     *         element.
     */
    public abstract String getPredicateNameCombinationString();

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement#getDefiningAxiom
     * (de.uka.ilkd.key.logic.Term, de.uka.ilkd.key.java.Services)
     */
    @Override
    public Term getDefiningAxiom(Term varOrConst, Services services) {
        TermBuilder tb = services.getTermBuilder();

        if (topElem) {
            return tb.tt();
        }

        if (predicates.size() == 0) {
            return tb.ff();
        }

        Term result = null;
        for (AbstractionPredicate pred : predicates) {
            Term application = pred.apply(varOrConst);
            if (result == null) {
                result = application;
            }
            else {
                result = combinePredicates(result, application, services);
            }
        }

        return result;
    }

    /**
     * Combines the given predicate terms (classically using AND or OR).
     * 
     * @param preds
     *            Term with all previous predicates.
     * @param newPred
     *            The new predicate to combine preds with.
     * @param services
     *            The services object.
     * @return The combination of preds with newPred.
     */
    protected abstract Term combinePredicates(Term preds, Term newPred,
            Services services);

    @Override
    public abstract boolean equals(Object obj);
}
