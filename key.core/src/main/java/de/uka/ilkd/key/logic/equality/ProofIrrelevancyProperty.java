/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.equality;


import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;

import org.key_project.util.EqualsModProofIrrelevancy;
import org.key_project.util.EqualsModProofIrrelevancyUtil;
import org.key_project.util.collection.ImmutableArray;

import java.util.Objects;

public class ProofIrrelevancyProperty implements TermProperty {
    /**
     * The single instance of this property.
     */
    public static final ProofIrrelevancyProperty PROOF_IRRELEVANCY_PROPERTY =
        new ProofIrrelevancyProperty();

    /**
     * This constructor is private as a single instance of this class should be shared. The instance
     * can be accessed
     * through {@link ProofIrrelevancyProperty#PROOF_IRRELEVANCY_PROPERTY} and is used as a
     * parameter for
     * {@link TermProperty#equalsModThisProperty(Term, Object)}.
     */
    private ProofIrrelevancyProperty() {}

    /**
     * Checks if {@code o} is a term syntactically equal to {@code term}, except for attributes that
     * are not relevant for the purpose of these terms in the proof.
     * <p>
     * Combines the prior implementations of {@link EqualsModProofIrrelevancy} in TermImpl and
     * LabeledTermImpl.
     * </p>
     *
     * @param term a term
     * @param o the object compared to {@code term}
     * @return true iff {@code o} is a term syntactically equal to {@code term}, except for
     *         proof-irrelevant attributes.
     */
    @Override
    public Boolean equalsModThisProperty(Term term, Object o) {
        if (o == term) {
            return true;
        }

        if (!(o instanceof Term other)) {
            return false;
        }

        final boolean opResult = term.op().equalsModProofIrrelevancy(other.op());
        if (!(opResult
                && EqualsModProofIrrelevancyUtil.compareImmutableArrays(term.boundVars(),
                    other.boundVars())
                && term.javaBlock().equalsModProofIrrelevancy(other.javaBlock()))) {
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
            if (!termSubs.get(i).equalsModProperty(PROOF_IRRELEVANCY_PROPERTY, otherSubs.get(i))) {
                return false;
            }
        }

        // This would be the only new thing from LabeledTermImpl, but this doesn't seem right
        if (term.hasLabels() && other.hasLabels()) {
            if (other.getLabels().size() != term.getLabels().size()) {
                return false;
            }
        }

        return true;
    }

    /**
     * <p>
     * Computes a hashcode that represents the proof-relevant fields of {@code term}.
     * </p>
     * Combines the prior implementations of {@link EqualsModProofIrrelevancy} in TermImpl and
     * LabeledTermImpl.
     *
     * @param term the term to compute the hashcode for
     * @return the hashcode
     */
    @Override
    public int hashCodeModThisProperty(Term term) {
        int hashcode2 = -1; // this line is just so the code compiles
        // part from TermImpl
        if (hashcode2 == -1) {
            // compute into local variable first to be thread-safe.
            hashcode2 = Objects.hash(term.op(), hashCodeIterable(term.subs()),
                EqualsModProofIrrelevancyUtil.hashCodeIterable(term.boundVars()), term.javaBlock());
            if (hashcode2 == -1) {
                hashcode2 = 0;
            }
        }
        // part from LabeledTermImpl
        final ImmutableArray<TermLabel> labels = term.getLabels();
        final int numOfLabels = labels.size();
        for (int i = 0; i < numOfLabels; i++) {
            final TermLabel currentLabel = labels.get(i);
            if (currentLabel.isProofRelevant()) {
                hashcode2 += 7 * currentLabel.hashCode();
            }
        }
        return hashcode2;
        // throw new UnsupportedOperationException(
        // "Hashing of terms modulo term proof-irrelevancy not yet implemented!");
    }

    // -------------------------- Utility methods --------------------------------- //

    /**
     * Compute the hashcode of an iterable of terms using the elements' {@link TermEqualsModProperty}
     * implementation.
     *
     * @param iter iterable of terms
     * @return combined hashcode
     */
    public static int hashCodeIterable(Iterable<? extends Term> iter) {
        // adapted from Arrays.hashCode
        if (iter == null) {
            return 0;
        }

        int result = 1;

        for (Term element : iter) {
            result = 31 * result + (element == null ? 0 : element.hashCodeModProperty(PROOF_IRRELEVANCY_PROPERTY));
        }

        return result;
    }
}
