/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.label.TermLabel;

import org.key_project.util.collection.ImmutableArray;

public class IrrelevantTermLabelsProperty implements TermProperty {
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

        ImmutableArray<TermLabel> termLabels = term.getLabels();
        ImmutableArray<TermLabel> otherLabels = other.getLabels();
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

        ImmutableArray<Term> termSubs = term.subs();
        ImmutableArray<Term> otherSubs = other.subs();
        final int numOfSubs = termSubs.size();
        for (int i = 0; i < numOfSubs; ++i) {
            if (!termSubs.get(i).equalsModIrrelevantTermLabels(otherSubs.get(i))) {
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
