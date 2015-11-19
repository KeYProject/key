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
import de.uka.ilkd.key.axiom_abstraction.AbstractionPredicate;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

/**
 * An abstract domain element for a predicate abstraction lattice.
 *
 * @author Dominic Scheurer
 */
public class PredicateAbstractionDomainElement extends AbstractDomainElement {
    
    /**
     * The bottom element of any predicate abstraction lattice.
     */
    public static final PredicateAbstractionDomainElement BOTTOM =
        new PredicateAbstractionDomainElement(false);
    
    /**
     * The top element of any predicate abstraction lattice.
     */
    public static final PredicateAbstractionDomainElement TOP =
        new PredicateAbstractionDomainElement(true);
    
    private ImmutableSet<AbstractionPredicate> predicates = null;
    private boolean isTopElem = false;
    

    /**
     * Constructs a new {@link PredicateAbstractionDomainElement} from a given
     * list of abstraction predicates.
     */
    public PredicateAbstractionDomainElement(
            final ImmutableSet<AbstractionPredicate> predicates) {
        this.predicates = predicates;
    }

    /**
     * Constructs a new {@link PredicateAbstractionDomainElement} that is
     * a top element if isTopElem is set to true; otherwise, it is a bottom
     * element.
     */
    private PredicateAbstractionDomainElement(boolean isTopElem) {
        this.predicates = DefaultImmutableSet.<AbstractionPredicate>nil();
        this.isTopElem = isTopElem;
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
        if (isTopElem) {
            return new Name("TOP");
        }
        
        if (predicates.size() == 0) {
            return new Name("BOTTOM");
        }

        StringBuilder result = new StringBuilder();
        for (AbstractionPredicate pred : predicates) {
            result.append("(" + pred.name() + ")").append("&");
        }
        result.deleteCharAt(result.length() - 1);

        return new Name(result.toString());
    }

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

        if (predicates.size() == 0) {
            return tb.ff();
        }
        
        if (isTopElem) {
            return tb.tt();
        }

        Term result = null;
        for (AbstractionPredicate pred : predicates) {
            Term application = pred.apply(varOrConst);
            if (result == null) {
                result = pred.apply(application);
            }
            else {
                result = tb.and(result, application);
            }
        }

        return result;
    }
    
    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        return obj instanceof PredicateAbstractionDomainElement &&
                (this != TOP || obj == TOP) &&
                (this != BOTTOM || obj == BOTTOM) &&
                this.predicates.equals(((PredicateAbstractionDomainElement)obj).predicates);
    }

}
