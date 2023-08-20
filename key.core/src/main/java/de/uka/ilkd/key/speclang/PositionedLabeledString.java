/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.parser.Location;

import org.key_project.util.collection.ImmutableArray;

/**
 * A positionedString with labels, which can then be passed over to the translated term. For the
 * moment, this is used to distinguish implicit specifications from explicit ones and '&' from '&&'
 * (logical and shortcut 'and') as well as '|' from '||' (logical and shortcut 'or'). Cf.
 * {@link de.uka.ilkd.key.logic.TermImpl} and {@link de.uka.ilkd.key.logic.LabeledTermImpl}.
 *
 * @author Michael Kirsten
 */
public class PositionedLabeledString extends PositionedString {

    public final ImmutableArray<TermLabel> labels;

    public PositionedLabeledString(String text, Location location,
            ImmutableArray<TermLabel> labels) {
        super(text, location);
        assert labels != null : "Term labels must not be null";
        assert !labels.isEmpty() : "There must be at least one term label";
        this.labels = labels;

    }

    public PositionedLabeledString(String text, Location location, TermLabel label) {
        this(text, location, new ImmutableArray<>(label));
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean hasLabels() {
        return true;
    }

    /**
     * returns the labels attached to this positioned string
     */
    @Override
    public ImmutableArray<TermLabel> getLabels() {
        return labels;
    }

    /**
     * returns true if the given label is attached
     *
     * @param label the ITermLabel for which to look (must not be null)
     * @return true iff. the label is attached to this positioned string
     */
    @Override
    public boolean containsLabel(TermLabel label) {
        assert label != null : "Label must not be null";
        for (TermLabel l : labels) {
            if (label.equals(l)) {
                return true;
            }
        }
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(Object o) {
        if (!(o instanceof PositionedLabeledString)) {
            return false;
        }
        final PositionedLabeledString cmp = (PositionedLabeledString) o;
        if (labels.size() == cmp.labels.size()) {
            if (!super.equals(o)) {
                return false;
            }
            for (TermLabel l : labels) { // this is not optimal, but as long as number of labels
                                         // limited ok
                if (!cmp.labels.contains(l)) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        return super.hashCode() * 17 + labels.hashCode();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        StringBuilder result = new StringBuilder(super.toString());
        result.append("<<");
        // as labels must not be empty at least one element exists
        result.append(labels.get(0).toString());
        for (int i = 1; i < labels.size(); i++) {
            result.append(", \"");
            result.append(labels.get(i).toString());
            result.append("\"");
        }
        result.append(">>");
        return result.toString();
    }
}
