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

package de.uka.ilkd.key.axiom_abstraction;

import java.util.function.Function;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

/**
 * Interface for predicates used for predicate abstraction. An abstraction
 * predicate is a mapping from program variables or constants to formulae
 * instantiated for the respective variable.
 *
 * @author Dominic Scheurer
 */
public abstract class AbstractionPredicate implements Function<Term, Term>,
        Named {

    /*
     * (non-Javadoc)
     * 
     * @see java.util.function.Function#apply(java.lang.Object)
     */
    @Override
    public abstract Term apply(Term t);

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return name().toString();
    }

    /**
     * Creates a new {@link AbstractionPredicate} with the given name and
     * mapping. You may use nice Java 8 lambdas for the second argument!
     *
     * @param name
     *            The name for the abstraction predicate, e.g. "_>0".
     * @param mapping
     *            The mapping from input terms of the adequate type to formulae,
     *            e.g. "(Term input) -> (tb.gt(input, tb.zero()))" where tb is a
     *            {@link TermBuilder}.
     * @return
     */
    public static AbstractionPredicate create(final String name,
            final Function<Term, Term> mapping) {
        return new AbstractionPredicate() {
            @Override
            public Term apply(Term input) {
                return mapping.apply(input);
            }

            @Override
            public Name name() {
                return new Name(name);
            }
        };
    }

}
