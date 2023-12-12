/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.equality;

import de.uka.ilkd.key.logic.Term;

import org.key_project.util.collection.ImmutableArray;

public class TermLabelsProperty implements TermProperty {
    /**
     * The single instance of this property.
     */
    public static final TermLabelsProperty TERM_LABELS_PROPERTY = new TermLabelsProperty();

    /**
     * This constructor is private as a single instance of this class should be shared. The instance
     * can be accessed
     * through {@link TermLabelsProperty#TERM_LABELS_PROPERTY} and is used as a parameter for
     * {@link TermProperty#equalsModThisProperty(Term, Object)}.
     */
    private TermLabelsProperty() {}

    @Override
    public Boolean equalsModThisProperty(Term term, Object o) {
        if (o == term) {
            return true;
        }

        if (!(o instanceof Term other)) {
            return false;
        }

        if (!(term.op().equals(other.op()) && term.boundVars().equals(other.boundVars())
                && term.javaBlock().equals(other.javaBlock()))) {
            return false;
        }

        final ImmutableArray<Term> termSubs = term.subs();
        final ImmutableArray<Term> otherSubs = other.subs();
        final int numOfSubs = termSubs.size();
        for (int i = 0; i < numOfSubs; ++i) {
            if (!termSubs.get(i).equalsModTermLabels(otherSubs.get(i))) {
                return false;
            }
        }
        return true;
    }

    @Override
    public int hashCodeModThisProperty(Term term) {
        throw new UnsupportedOperationException(
            "Hashing of terms modulo term labels not yet implemented!");
    }
}
