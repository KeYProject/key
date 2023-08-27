/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.axiom_abstraction.predicateabstraction;

import java.util.Iterator;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

/**
 * A base class for abstract domain elements in a predicate abstraction lattice.
 *
 * @author Dominic Scheurer
 */
public abstract class AbstractPredicateAbstractionDomainElement extends AbstractDomainElement {

    private ImmutableSet<AbstractionPredicate> predicates = null;
    private boolean topElem = false;

    /**
     * Constructs a new {@link AbstractPredicateAbstractionDomainElement} from a given list of
     * abstraction predicates.
     */
    public AbstractPredicateAbstractionDomainElement(
            final ImmutableSet<AbstractionPredicate> predicates) {
        this.predicates = predicates;
    }

    /**
     * Constructs a new {@link AbstractPredicateAbstractionDomainElement} that is a top element if
     * isTopElem is set to true; otherwise, it is a bottom element.
     */
    protected AbstractPredicateAbstractionDomainElement(boolean isTopElem) {
        this.predicates = DefaultImmutableSet.nil();
        this.topElem = isTopElem;
    }

    /**
     * @return Whether this element is the top element of the lattice (the axiom of which is true
     *         for every input).
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
     * @param predicates the abstraction predicates for this domain element to set.
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

    @Override
    public String toString() {
        return name().toString();
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement#getDefiningAxiom
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
            } else {
                result = combinePredicates(result, application, services);
            }
        }

        return result;
    }

    /**
     * Combines the given predicate terms (classically using AND or OR).
     *
     * @param preds Term with all previous predicates.
     * @param newPred The new predicate to combine preds with.
     * @param services The services object.
     * @return The combination of preds with newPred.
     */
    protected abstract Term combinePredicates(Term preds, Term newPred, Services services);

    /**
     * NOTE: This method should be defined in accordance with
     * {@link AbstractPredicateAbstractionLattice#getPredicateNameCombinationString()} . This is
     * probably bad design, but a substitute of the Java shortcoming that there are no abstract
     * static methods.
     *
     * @return The String which is used for combining the names of predicates for lattice types
     *         where multiple predicates determine an abstract element.
     */
    public abstract String getPredicateNameCombinationString();

    @Override
    public String toParseableString(Services services) {
        final StringBuilder sb = new StringBuilder();

        final Iterator<AbstractionPredicate> it = getPredicates().iterator();
        while (it.hasNext()) {
            sb.append(it.next().toParseableString(services));
            if (it.hasNext()) {
                sb.append(getPredicateNameCombinationString());
            }
        }

        return sb.toString();
    }

    @Override
    public abstract boolean equals(Object obj);

    @Override
    public abstract int hashCode();
}
