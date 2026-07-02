/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.equality;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.util.EqualityUtils;

import org.key_project.logic.Property;
import org.key_project.util.collection.ImmutableArray;

/**
 * A property that can be used in
 * {@link EqualsModProperty#equalsModProperty(Object, Property, Object[])} for terms.
 * All irrelevant term labels are ignored in this equality check.
 * <p>
 * The single instance of this property can be accessed through
 * {@link IrrelevantTermLabelsProperty#IRRELEVANT_TERM_LABELS_PROPERTY}.
 *
 * @author Tobias Reinhold
 */
public class IrrelevantTermLabelsProperty implements Property<JTerm> {
    /**
     * The single instance of this property.
     */
    public static final IrrelevantTermLabelsProperty IRRELEVANT_TERM_LABELS_PROPERTY =
        new IrrelevantTermLabelsProperty();

    /**
     * This constructor is private as a single instance of this class should be shared. The instance
     * can be accessed through {@link IrrelevantTermLabelsProperty#IRRELEVANT_TERM_LABELS_PROPERTY}
     * and is used as a parameter for
     * {@link EqualsModProperty#equalsModProperty(Object, Property, Object[])}.
     */
    private IrrelevantTermLabelsProperty() {}

    /**
     * Checks if {@code term2} is a term syntactically equal to {@code term1}, except for some
     * irrelevant labels.
     *
     * @param term1 a term
     * @param term2 the term compared to {@code term1}
     * @param v should not be used for this equality check
     * @return {@code true} iff {@code term2} is a term syntactically equal to {@code term1}, except
     *         for their irrelevant labels.
     * @param <V> is not needed for this equality check
     * @see TermLabel#isProofRelevant() isStrategyRelevant
     */
    @Override
    public <V> boolean equalsModThisProperty(JTerm term1, JTerm term2, V... v) {
        if (term2 == term1) {
            return true;
        }

        if (!(term1.op().equals(term2.op()) && term1.boundVars().equals(term2.boundVars())
                && term1.javaBlock().equals(term2.javaBlock()))) {
            return false;
        }

        final ImmutableArray<TermLabel> term1Labels = term1.getLabels();
        final ImmutableArray<TermLabel> term2Labels = term2.getLabels();
        for (TermLabel label : term1Labels) {
            if (label.isProofRelevant() && !term2Labels.contains(label)) {
                return false;
            }
        }
        for (TermLabel label : term2Labels) {
            if (label.isProofRelevant() && !term1Labels.contains(label)) {
                return false;
            }
        }

        final ImmutableArray<JTerm> termSubs = term1.subs();
        final ImmutableArray<JTerm> term2Subs = term2.subs();
        final int numOfSubs = termSubs.size();
        for (int i = 0; i < numOfSubs; ++i) {
            if (!termSubs.get(i).equalsModProperty(term2Subs.get(i),
                IRRELEVANT_TERM_LABELS_PROPERTY)) {
                return false;
            }
        }

        return true;
    }

    /**
     * Computes the hash code of {@code term} while ignoring irrelevant labels.
     *
     * @param term the term to compute the hash code for
     * @return the hash code
     */
    @Override
    public int hashCodeModThisProperty(JTerm term) {
        int hashcode = 5;
        hashcode = hashcode * 17 + term.op().hashCode();
        hashcode = hashcode * 17 + EqualityUtils
                .hashCodeModPropertyOfIterable(term.subs(), this::hashCodeModThisProperty);
        hashcode = hashcode * 17 + term.boundVars().hashCode();
        hashcode = hashcode * 17 + term.javaBlock().hashCode();

        final ImmutableArray<TermLabel> labels = term.getLabels();
        for (int i = 0, sz = labels.size(); i < sz; i++) {
            final TermLabel currentLabel = labels.get(i);
            if (currentLabel.isProofRelevant()) {
                hashcode += 7 * currentLabel.hashCode();
            }
        }

        return hashcode;
    }
}
