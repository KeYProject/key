/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.strategy.feature.MutableState;

/**
 * A termfeature that can be used to check whether a term has a specific label
 * {@link #create(TermLabel)} or any label {{@link #HAS_ANY_LABEL} at all.
 */
public class TermLabelTermFeature extends BinaryTermFeature {

    public static final TermFeature HAS_ANY_LABEL = new TermLabelTermFeature(null);

    public static TermFeature create(TermLabel label) {
        return new TermLabelTermFeature(label);
    }


    private final TermLabel label;

    private TermLabelTermFeature(TermLabel label) {
        this.label = label;
    }

    @Override
    protected boolean filter(Term term, MutableState mState, Services services) {
        if (label == null) {
            return term.hasLabels();
        }
        return term.containsLabel(label);
    }
}
