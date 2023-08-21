/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.Objects;
import java.util.stream.Collectors;

import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

import org.key_project.util.EqualsModProofIrrelevancy;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.java.CollectionUtil;

/**
 * The labeled term class is used for terms that have a label attached.
 *
 * Two labeled terms are equal if they have equal term structure and equal annotations. In contrast
 * the method {@link Term#equalsModRenaming(Object)} does not care about annotations and will just
 * compare the term structure alone modula renaming.
 *
 * @see Term
 * @see TermImpl
 */
class LabeledTermImpl extends TermImpl implements EqualsModProofIrrelevancy {

    /**
     * @see #getLabels()
     */
    private final ImmutableArray<TermLabel> labels;

    /**
     * creates an instance of a labeled term.
     *
     * @param op the top level operator
     * @param subs the Term that are the subterms of this term
     * @param boundVars logic variables bound by the operator
     * @param javaBlock contains the program part of the term (if any)
     * @param labels the terms labels (must not be null or empty)
     */
    public LabeledTermImpl(Operator op, ImmutableArray<Term> subs,
            ImmutableArray<QuantifiableVariable> boundVars, JavaBlock javaBlock,
            ImmutableArray<TermLabel> labels) {
        super(op, subs, boundVars, javaBlock);
        assert labels != null : "Term labels must not be null";
        assert !labels.isEmpty() : "There must be at least one term label";
        this.labels = labels;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean hasLabels() {
        return true;
    }

    /**
     * returns the labels attached to this term
     */
    @Override
    public ImmutableArray<TermLabel> getLabels() {
        return labels;
    }

    @Override
    public TermLabel getLabel(final Name termLabelName) {
        return CollectionUtil.search(labels,
            element -> Objects.equals(element.name(), termLabelName));
    }

    /**
     * returns true if the given label is attached
     *
     * @param label the TermLabel for which to look (must not be null)
     * @return true iff. the label is attached to this term
     */
    @Override
    public boolean containsLabel(TermLabel label) {
        assert label != null : "Label must not be null";
        for (int i = 0, sz = labels.size(); i < sz; i++) {
            if (label.equals(labels.get(i))) {
                return true;
            }
        }
        return false;
    }

    @Override
    public boolean equals(Object o) {
        if (!super.equals(o)) {
            return false;
        }

        final LabeledTermImpl cmp = (LabeledTermImpl) o;
        if (labels.size() == cmp.labels.size()) {
            for (int i = 0, sz = labels.size(); i < sz; i++) {
                // this is not optimal, but as long as number of labels limited ok
                if (!cmp.labels.contains(labels.get(i))) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    @Override
    public int computeHashCode() {
        int hash = super.computeHashCode();
        for (int i = 0, sz = labels.size(); i < sz; i++) {
            hash += 7 * labels.get(i).hashCode();
        }
        return hash;
    }

    @Override
    public boolean equalsModProofIrrelevancy(Object o) {
        if (!super.equalsModProofIrrelevancy(o)) {
            return false;
        }

        if (o instanceof LabeledTermImpl) {
            final LabeledTermImpl cmp = (LabeledTermImpl) o;
            if (labels.size() == cmp.labels.size()) {
                for (int i = 0, sz = labels.size(); i < sz; i++) {
                    // skip irrelevant (origin) labels that differ for no real reason
                    if (!labels.get(i).isProofRelevant()) {
                        continue;
                    }
                    // this is not optimal, but as long as number of labels limited ok
                    if (!cmp.labels.contains(labels.get(i))) {
                        return false;
                    }
                }
                return true;
            }
            return false;
        } else {
            return o.getClass() == TermImpl.class;
        }
    }

    @Override
    public int hashCodeModProofIrrelevancy() {
        int hash = super.hashCodeModProofIrrelevancy();
        for (int i = 0, sz = labels.size(); i < sz; i++) {
            if (labels.get(i).isProofRelevant()) {
                hash += 7 * labels.get(i).hashCode();
            }
        }
        return hash;
    }

    @Override
    public String toString() {
        StringBuilder result = new StringBuilder(super.toString());

        String labelsStr = labels.stream()
                // .filter(TermLabel::isProofRelevant)
                .map(TermLabel::toString).collect(Collectors.joining(", "));

        if (!labelsStr.isEmpty()) {
            result.append("<<");
            result.append(labelsStr);
            result.append(">>");
        }

        return result.toString();
    }
}
