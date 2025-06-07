/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.equality;

import de.uka.ilkd.key.logic.util.EqualityUtils;

import org.key_project.logic.Property;
import org.key_project.logic.Term;
import org.key_project.logic.op.Modality;

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

        if (!(term1.op().equals(term2.op()) && term1.boundVars().equals(term2.boundVars()))) {
            return false;
        }

        if (term1.op() instanceof Modality mod1
                && !(mod1.programBlock().equals(((Modality) (term2.op())).programBlock()))) {
            return false;
        }

        final var term1Subs = term1.subs();
        final var term2Subs = term2.subs();
        final int numOfSubs = term1Subs.size();
        for (int i = 0; i < numOfSubs; ++i) {
            if (!this.equalsModThisProperty(term1Subs.get(i), term2Subs.get(i))) {
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
                + EqualityUtils.hashCodeModPropertyOfIterable(term.subs(),
                    this::hashCodeModThisProperty);
        hashcode = hashcode * 17 + term.boundVars().hashCode();
        hashcode =
            hashcode * 17 + (term.op() instanceof Modality mod ? mod.programBlock().hashCode() : 3);

        return hashcode;
    }

}
