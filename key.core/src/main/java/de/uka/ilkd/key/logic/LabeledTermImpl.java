/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.Objects;
import java.util.stream.Collectors;

import de.uka.ilkd.key.logic.equality.EqualsModProperty;
import de.uka.ilkd.key.logic.equality.RenamingTermProperty;
import de.uka.ilkd.key.logic.label.TermLabel;

import org.key_project.logic.Name;
import org.key_project.logic.Property;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.java.CollectionUtil;

/**
 * <p>
 * The labeled term class is used for terms that have a label attached.
 * </p>
 *
 * Two labeled terms are equal if they have equal term structure and equal annotations. In contrast,
 * the method {@link EqualsModProperty#equalsModProperty(Object, Property, Object[])} can be used to
 * compare terms
 * while ignoring certain
 * given properties. E.g. by using {@link RenamingTermProperty#RENAMING_TERM_PROPERTY}, just the
 * term structures modulo
 * renaming are compared whilst ignoring annotations. *
 *
 * @see JTerm
 * @see TermImpl
 */
class LabeledTermImpl extends TermImpl {

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
     * @param labels the term's labels (must not be null or empty)
     * @param origin a String with origin information
     */
    public LabeledTermImpl(Operator op, ImmutableArray<JTerm> subs,
            ImmutableArray<QuantifiableVariable> boundVars,
            ImmutableArray<TermLabel> labels, String origin) {
        super(op, subs, boundVars, origin);
        assert labels != null : "Term labels must not be null";
        assert !labels.isEmpty() : "There must be at least one term label";
        this.labels = labels;
    }

    /**
     * creates an instance of a labeled term.
     *
     * @param op the top level operator
     * @param subs the Term that are the subterms of this term
     * @param boundVars logic variables bound by the operator
     * @param labels the terms labels (must not be null or empty)
     */
    public LabeledTermImpl(Operator op, ImmutableArray<JTerm> subs,
            ImmutableArray<QuantifiableVariable> boundVars,
            ImmutableArray<TermLabel> labels) {
        super(op, subs, boundVars, "");
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
        if (o == this) {
            return true;
        }

        if (o instanceof final LabeledTermImpl cmp) {
            if (labels.size() != cmp.labels.size()) {
                return false;
            }

            if (!super.equals(o)) {
                return false;
            }

            if (labels.size() == cmp.labels.size()) {
                for (int i = 0, sz = labels.size(); i < sz; i++) {
                    // this is not optimal, but as long as number of labels limited ok
                    if (!cmp.labels.contains(labels.get(i))) {
                        return false;
                    }
                }
                return true;
            }
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
