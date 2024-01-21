/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.equality;

import de.uka.ilkd.key.logic.Term;

import org.key_project.util.collection.ImmutableArray;

/**
 * A property that can be used in
 * {@link TermEqualsModProperty#equalsModProperty(Object, TermProperty)}.
 * All term labels are ignored in this equality check.
 */
public class TermLabelsProperty implements TermProperty {
    /**
     * The single instance of this property.
     */
    public static final TermLabelsProperty TERM_LABELS_PROPERTY = new TermLabelsProperty();

    /**
     * This constructor is private as a single instance of this class should be shared. The instance
     * can be accessed
     * through {@link TermLabelsProperty#TERM_LABELS_PROPERTY} and is used as a parameter for
     * {@link TermProperty#equalsModThisProperty(Term, Term)}.
     */
    private TermLabelsProperty() {}

    /**
     * Checks if {@code term2} is a term syntactically equal to {@code term1}, ignoring <b>all</b>
     * term
     * labels.
     *
     * @param term1 a term
     * @param term2 the term compared to {@code term1}
     * @return {@code true} iff {@code term2} is a term syntactically equal to {@code term1}
     *         ignoring <b>all</b>
     *         term labels
     */
    @Override
    public Boolean equalsModThisProperty(Term term1, Term term2) {
        if (term2 == term1) {
            return true;
        }

        if (!(term1.op().equals(term2.op()) && term1.boundVars().equals(term2.boundVars())
                && term1.javaBlock().equals(term2.javaBlock()))) {
            return false;
        }

        final ImmutableArray<Term> term1Subs = term1.subs();
        final ImmutableArray<Term> term2Subs = term2.subs();
        final int numOfSubs = term1Subs.size();
        for (int i = 0; i < numOfSubs; ++i) {
            if (!term1Subs.get(i).equalsModProperty(term2Subs.get(i), TERM_LABELS_PROPERTY)) {
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
