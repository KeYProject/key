/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.equality;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.util.EqualityUtils;

import org.key_project.util.collection.ImmutableArray;

/**
 * A property that can be used in
 * {@link EqualsModProperty#equalsModProperty(Object, Property, Object[])} for terms.
 * All term labels are ignored in this equality check.
 * <p>
 * The single instance of this property can be accessed through
 * {@link TermLabelsProperty#TERM_LABELS_PROPERTY}.
 *
 * @author Tobias Reinhold
 */
public class TermLabelsProperty implements Property<Term> {
    /**
     * The single instance of this property.
     */
    public static final TermLabelsProperty TERM_LABELS_PROPERTY = new TermLabelsProperty();

    /**
     * This constructor is private as a single instance of this class should be shared. The instance
     * can be accessed through {@link TermLabelsProperty#TERM_LABELS_PROPERTY} and is used as a
     * parameter for {@link EqualsModProperty#equalsModProperty(Object, Property, Object[])}.
     */
    private TermLabelsProperty() {}

    /**
     * Checks if {@code term2} is a term syntactically equal to {@code term1}, ignoring <b>all</b>
     * term labels.
     *
     * @param term1 a term
     * @param term2 the term compared to {@code term1}
     * @param v should not be used for this equality check
     * @return {@code true} iff {@code term2} is a term syntactically equal to {@code term1}
     *         ignoring <b>all</b> term labels
     * @param <V> is not needed for this equality check
     */
    @Override
    public <V> boolean equalsModThisProperty(Term term1, Term term2, V... v) {
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

    /**
     * Computes the hash code of {@code term} while ignoring <b>all</b> term labels.
     *
     * @param term the term to compute the hash code for
     * @return the hash code
     */
    @Override
    public int hashCodeModThisProperty(Term term) {
        /*
         * Currently, the hash code is computed almost the same way as in TermImpl. This is also the
         * case for labeled terms, as all term labels are ignored.
         */
        int hashcode = 5;
        hashcode = hashcode * 17 + term.op().hashCode();
        hashcode = hashcode * 17
                + EqualityUtils.hashCodeModPropertyOfIterable(TERM_LABELS_PROPERTY, term.subs());
        hashcode = hashcode * 17 + term.boundVars().hashCode();
        hashcode = hashcode * 17 + term.javaBlock().hashCode();

        return hashcode;
    }

}
