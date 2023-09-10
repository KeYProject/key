/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.function.Function;
import java.util.function.Predicate;

import de.uka.ilkd.key.java.Services;

/**
 * A generic {@link Term} replace visitor based on a filter predicate and a replacement function for
 * the filtered subterms.
 *
 * @author Dominic Steinhoefel
 */
public class GenericTermReplacer {
    public static Term replace(final Term t, final Predicate<Term> filter,
            final Function<Term, Term> replacer, Services services) {
        Term newTopLevelTerm = t;
        if (filter.test(t)) {
            newTopLevelTerm = replacer.apply(t);
        }

        final Term[] newSubs =
            newTopLevelTerm.subs().stream().map(sub -> replace(sub, filter, replacer, services))
                    .toArray(Term[]::new);

        return services.getTermFactory().createTerm(newTopLevelTerm.op(), newSubs,
            newTopLevelTerm.boundVars(), newTopLevelTerm.javaBlock(), newTopLevelTerm.getLabels());
    }
}
