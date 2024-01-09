/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.equality;

import de.uka.ilkd.key.logic.Term;

import org.key_project.util.collection.ImmutableArray;

/**
 * A property that can be used in
 * {@link TermEqualsModProperty#equalsModProperty(TermProperty, Object)}.
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
     * {@link TermProperty#equalsModThisProperty(Term, Object)}.
     */
    private TermLabelsProperty() {}

    /**
     * Checks if {@code o} is a term syntactically equal to {@code term}, ignoring <b>all</b> term
     * labels.
     *
     * @param term a term
     * @param o the object compared to {@code term}
     * @return {@code true} iff {@code o} is a term syntactically equal to this ignoring <b>all</b>
     *         term labels
     */
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
            if (!termSubs.get(i).equalsModProperty(TERM_LABELS_PROPERTY, otherSubs.get(i))) {
                return false;
            }
        }
        return true;
    }

    /**
     * Computes the hash code of {@code term} while ignoring <b>all</b> term labels.
     * <p>
     * Currently, the hash code is computed almost the same way as in TermImpl. This is also the
     * case for labeled terms,
     * as all term labels are ignored.
     *
     * @param term the term to compute the hash code for
     * @return the hash code
     */
    @Override
    public int hashCodeModThisProperty(Term term) {
        // change 5 and 17 not to match TermImpl's implementation too much
        int hashcode = 5;
        hashcode = hashcode * 17 + term.op().hashCode();
        hashcode = hashcode * 17
                + EqualityUtils.hashCodeModPropertyOfIterable(TERM_LABELS_PROPERTY, term.subs());
        hashcode = hashcode * 17 + term.boundVars().hashCode();
        hashcode = hashcode * 17 + term.javaBlock().hashCode();

        return hashcode;
    }

}
