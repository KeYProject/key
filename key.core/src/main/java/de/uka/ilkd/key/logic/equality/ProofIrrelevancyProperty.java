/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.equality;


import java.util.Objects;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.util.EqualityUtils;
import de.uka.ilkd.key.rule.EqualityModuloProofIrrelevancy;

import org.key_project.logic.Property;
import org.key_project.util.EqualsModProofIrrelevancyUtil;
import org.key_project.util.collection.ImmutableArray;


/**
 * A property that can be used in
 * {@link EqualsModProperty#equalsModProperty(Object, Property, Object[])} for terms.
 * All proof irrelevant attributes are ignored in this equality check.
 * <p>
 * The single instance of this property can be accessed through
 * {@link ProofIrrelevancyProperty#PROOF_IRRELEVANCY_PROPERTY}.
 *
 * @author Tobias Reinhold
 */
public class ProofIrrelevancyProperty implements Property<JTerm> {
    /**
     * The single instance of this property.
     */
    public static final ProofIrrelevancyProperty PROOF_IRRELEVANCY_PROPERTY =
        new ProofIrrelevancyProperty();

    /**
     * This constructor is private as a single instance of this class should be shared. The instance
     * can be accessed through {@link ProofIrrelevancyProperty#PROOF_IRRELEVANCY_PROPERTY} and is
     * used as a parameter for
     * {@link EqualsModProperty#equalsModProperty(Object, Property, Object[])}.
     */
    private ProofIrrelevancyProperty() {}

    /**
     * Checks if {@code term2} is a term syntactically equal to {@code term1}, except for attributes
     * that are not relevant for the purpose of these terms in the proof.
     * <p>
     * Combines the prior implementations of {@code EqualsModProofIrrelevancy} in TermImpl and
     * LabeledTermImpl.
     * </p>
     *
     * @param term1 a term
     * @param term2 the term compared to {@code term1}
     * @param v should not be used for this equality check
     * @return true iff {@code term2} is a term syntactically equal to {@code term1}, except for
     *         proof-irrelevant attributes.
     * @param <V> is not needed for this equality check
     */
    @Override
    public <V> boolean equalsModThisProperty(JTerm term1, JTerm term2, V... v) {
        if (term2 == term1) {
            return true;
        }

        final boolean opResult =
            EqualityModuloProofIrrelevancy.equalsModProofIrrelevancy(term1.op(), term2.op());
        if (!(opResult
                && EqualsModProofIrrelevancyUtil.compareImmutableArrays(term1.boundVars(),
                    term2.boundVars(),
                    EqualityModuloProofIrrelevancy::equalsModProofIrrelevancy)
                && EqualityModuloProofIrrelevancy.equalsModProofIrrelevancy(term1.javaBlock(),
                    term2.javaBlock()))) {
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

        final ImmutableArray<JTerm> term1Subs = term1.subs();
        final ImmutableArray<JTerm> term2Subs = term2.subs();
        final int numOfSubs = term1Subs.size();
        for (int i = 0; i < numOfSubs; ++i) {
            if (!term1Subs.get(i).equalsModProperty(term2Subs.get(i), PROOF_IRRELEVANCY_PROPERTY)) {
                return false;
            }
        }

        return true;
    }

    /**
     * <p>
     * Computes a hashcode that represents the proof-relevant fields of {@code term}.
     * </p>
     *
     * @param term the term to compute the hashcode for
     * @return the hashcode
     */
    @Override
    public int hashCodeModThisProperty(JTerm term) {
        int hashcode = Objects.hash(term.op(),
            EqualityUtils.hashCodeModPropertyOfIterable(term.subs(), this::hashCodeModThisProperty),
            EqualsModProofIrrelevancyUtil.hashCodeIterable(term.boundVars(),
                EqualityModuloProofIrrelevancy::hashCodeModProofIrrelevancy),
            term.javaBlock());

        // part from LabeledTermImpl
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
