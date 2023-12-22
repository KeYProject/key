/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.equality;

import java.util.Objects;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;

import org.key_project.util.EqualsModProofIrrelevancyUtil;
import org.key_project.util.collection.ImmutableArray;

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
     * Checks if {@code o} is a term syntactically equal to {@code term}, except for attributes that are not relevant
     * for the purpose of these terms in the proof.
     *
     * @param term a term
     * @param o the object compared to {@code term}
     * @return true iff {@code o} is a term syntactically equal to {@code term}, except for proof-irrelevant attributes.
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

        return true;
    }

    /**
     * Computes a hashcode that represents the proof-relevant fields of {@code term}.
     *
     * @param term the term to compute the hashcode for
     * @return the hashcode
     */
    @Override
    public int hashCodeModThisProperty(Term term) {
        int hashcode2 = -1; // this line is just so the code compiles
        if (hashcode2 == -1) {
            // compute into local variable first to be thread-safe.
            hashcode2 = Objects.hash(term.op(),
                EqualsModProofIrrelevancyUtil
                        .hashCodeIterable(term.subs()),
                EqualsModProofIrrelevancyUtil.hashCodeIterable(term.boundVars()), term.javaBlock());
            if (hashcode2 == -1) {
                hashcode2 = 0;
            }
        }
        return hashcode2;
//        throw new UnsupportedOperationException("Hashing of terms modulo term proof-irrelevancy not yet implemented!");

    }
}
