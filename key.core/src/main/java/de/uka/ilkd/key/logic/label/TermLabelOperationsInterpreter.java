/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.label;

import java.util.HashSet;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.logic.Term;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * A collection of static methods to deal with {@link TermLabel}.
 *
 * @author Richard Bubel
 */
class TermLabelOperationsInterpreter {

    public static ImmutableArray<TermLabel> intersection(ImmutableArray<TermLabel> left,
            ImmutableArray<TermLabel> right) {
        final HashSet<TermLabel> set = new LinkedHashSet<>();
        for (TermLabel r : right) {
            if (left.contains(r)) {
                set.add(r);
            }
        }
        return new ImmutableArray<>(set.toArray(new TermLabel[0]));
    }

    public static ImmutableArray<TermLabel> union(ImmutableArray<TermLabel> left,
            ImmutableArray<TermLabel> right) {
        final HashSet<TermLabel> set = new LinkedHashSet<>();
        for (TermLabel l : left) {
            set.add(l);
        }
        for (TermLabel l : right) {
            set.add(l);
        }
        return new ImmutableArray<>(set.toArray(new TermLabel[0]));
    }

    public static ImmutableArray<TermLabel> sub(ImmutableArray<TermLabel> left,
            ImmutableArray<TermLabel> right) {
        final HashSet<TermLabel> set = new LinkedHashSet<>();
        for (TermLabel l : left) {
            set.add(l);
        }
        for (TermLabel l : right) {
            set.remove(l);
        }
        return new ImmutableArray<>(set.toArray(new TermLabel[0]));
    }

    /**
     * resolves term redundancy (used by Sequent to avoid duplicate formulas). In case of t2 being
     * unlabeled a list with t1 as single element is returned. Otherwise if t1 is unlabeled (and t2
     * labeled), then a list with t2 as single element is returned. If both terms are labeled a list
     * of terms is returned which is not redundant.
     *
     * The terms t1 and t2 may only differ in their attached labels. Otherwise they have to be
     * structural identical
     *
     * This method should be used in case to implement more complex redundancy checks.
     *
     * @param t1 the Term t1 which is structural equivalent to t2 (except maybe labels)
     * @param t2 the Term t2
     * @return a list which represents a redundancy free result of merging labels in t1 and t2
     */
    public static ImmutableList<Term> resolveRedundancy(Term t1, Term t2) {
        ImmutableList<Term> result = ImmutableSLList.nil();
        if (!t2.hasLabels()) {
            return result.prepend(t1);
        } else if (!t1.hasLabels()) {
            return result.prepend(t2);
        }

        for (int i = 0; i < t1.arity(); i++) {
            if (!t1.sub(i).equals(t2.sub(i))) {

            }
        }

        return null;
    }

}
