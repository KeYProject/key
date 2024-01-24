/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.equality;


import java.util.Objects;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.util.EqualityUtils;

import org.key_project.util.EqualsModProofIrrelevancy;
import org.key_project.util.EqualsModProofIrrelevancyUtil;
import org.key_project.util.collection.ImmutableArray;

/**
 * A property that can be used in
 * {@link TermEqualsModProperty#equalsModProperty(Object, TermProperty)}.
 * All proof irrelevant attributes are ignored in this equality check.
 */
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
     * {@link TermProperty#equalsModThisProperty(Term, Term)}.
     */
    private ProofIrrelevancyProperty() {}

    /**
     * Checks if {@code term2} is a term syntactically equal to {@code term1}, except for attributes
     * that
     * are not relevant for the purpose of these terms in the proof.
     * <p>
     * Combines the prior implementations of {@link EqualsModProofIrrelevancy} in TermImpl and
     * LabeledTermImpl.
     * </p>
     *
     * @param term1 a term
     * @param term2 the term compared to {@code term1}
     * @return true iff {@code term2} is a term syntactically equal to {@code term1}, except for
     *         proof-irrelevant attributes.
     */
    @Override
    public Boolean equalsModThisProperty(Term term1, Term term2) {
        if (term2 == term1) {
            return true;
        }

        final boolean opResult = term1.op().equalsModProofIrrelevancy(term2.op());
        if (!(opResult
                && EqualsModProofIrrelevancyUtil.compareImmutableArrays(term1.boundVars(),
                    term2.boundVars())
                && term1.javaBlock().equalsModProofIrrelevancy(term2.javaBlock()))) {
            return false;
        }

        final ImmutableArray<TermLabel> termLabels = term1.getLabels();
        final ImmutableArray<TermLabel> term2Labels = term2.getLabels();
        for (TermLabel label : termLabels) {
            if (label.isProofRelevant() && !term2Labels.contains(label)) {
                return false;
            }
        }
        for (TermLabel label : term2Labels) {
            if (label.isProofRelevant() && !termLabels.contains(label)) {
                return false;
            }
        }

        final ImmutableArray<Term> term1Subs = term1.subs();
        final ImmutableArray<Term> term2Subs = term2.subs();
        final int numOfSubs = term1Subs.size();
        for (int i = 0; i < numOfSubs; ++i) {
            if (!term1Subs.get(i).equalsModProperty(term2Subs.get(i), PROOF_IRRELEVANCY_PROPERTY)) {
                return false;
            }
        }

        // This would be the only new thing from LabeledTermImpl, but this doesn't seem right
        if (term1.hasLabels() && term2.hasLabels()) {
            if (term2.getLabels().size() != term1.getLabels().size()) {
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
            hashcode2 = Objects.hash(term.op(),
                EqualityUtils.hashCodeModPropertyOfIterable(PROOF_IRRELEVANCY_PROPERTY,
                    term.subs()),
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
    }
}
