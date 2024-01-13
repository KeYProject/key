/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.equality;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;

import org.key_project.util.collection.ImmutableArray;

/**
 * A property that can be used in
 * {@link TermEqualsModProperty#equalsModProperty(Object, TermProperty)}.
 * All irrelevant term labels are ignored in this equality check.
 */
public class IrrelevantTermLabelsProperty implements TermProperty {
    /**
     * The single instance of this property.
     */
    public static final IrrelevantTermLabelsProperty IRRELEVANT_TERM_LABELS_PROPERTY =
        new IrrelevantTermLabelsProperty();

    /**
     * This constructor is private as a single instance of this class should be shared. The instance
     * can be accessed
     * through {@link IrrelevantTermLabelsProperty#IRRELEVANT_TERM_LABELS_PROPERTY} and is used as a
     * parameter for
     * {@link TermProperty#equalsModThisProperty(Term, Object)}.
     */
    private IrrelevantTermLabelsProperty() {}

    /**
     * Checks if {@code o} is a term syntactically equal to {@code term}, except for some irrelevant
     * labels.
     *
     * @param term a term
     * @param o the object compared to {@code term}
     * @return {@code true} iff {@code o} is a term syntactically equal to {@code term}, except for
     *         their irrelevant labels.
     * @see TermLabel#isProofRelevant() isStrategyRelevant
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

        final ImmutableArray<TermLabel> termLabels = term.getLabels();
        final ImmutableArray<TermLabel> otherLabels = other.getLabels();
        for (TermLabel label : termLabels) {
            if (label.isProofRelevant() && !otherLabels.contains(label)) {
                return false;
            }
        }
        for (TermLabel label : otherLabels) {
            if (label.isProofRelevant() && !termLabels.contains(label)) {
                return false;
            }
        }

        final ImmutableArray<Term> termSubs = term.subs();
        final ImmutableArray<Term> otherSubs = other.subs();
        final int numOfSubs = termSubs.size();
        for (int i = 0; i < numOfSubs; ++i) {
            if (!termSubs.get(i).equalsModProperty(otherSubs.get(i),
                IRRELEVANT_TERM_LABELS_PROPERTY)) {
                return false;
            }
        }

        return true;
    }

    @Override
    public int hashCodeModThisProperty(Term term) {
        throw new UnsupportedOperationException(
            "Hashing of terms modulo irrelevant term labels not yet implemented!");
    }
}
