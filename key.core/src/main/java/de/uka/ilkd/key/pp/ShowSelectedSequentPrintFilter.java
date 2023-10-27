/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * This filter takes a {@link PosInOccurrence} and only shows the sub-formula at that position.
 *
 * @author lanzinger
 */
public class ShowSelectedSequentPrintFilter extends SequentPrintFilter {

    /**
     * The position of the only sub-formula to show.
     */
    private final PosInOccurrence pos;

    /**
     * Create a new {@link ShowSelectedSequentPrintFilter}.
     *
     * @param pos the position of the only sub-formula to show.
     */
    public ShowSelectedSequentPrintFilter(PosInOccurrence pos) {
        this.pos = pos;
    }

    @Override
    protected void filterSequent() {}

    @Override
    public ImmutableList<SequentPrintFilterEntry> getFilteredAntec() {
        if (pos.isInAntec()) {
            return ImmutableSLList.<SequentPrintFilterEntry>nil().append(new Entry(pos));
        } else {
            return ImmutableSLList.nil();
        }
    }

    @Override
    public ImmutableList<SequentPrintFilterEntry> getFilteredSucc() {
        if (!pos.isInAntec()) {
            return ImmutableSLList.<SequentPrintFilterEntry>nil().append(new Entry(pos));
        } else {
            return ImmutableSLList.nil();
        }
    }

    /**
     * An Entry in {@link accessibility} {@link ShowSelectedSequentPrintFilter}.
     *
     * The only entry created for such a filter contains the sub-term at the specified position as
     * filtered term ({@link #getFilteredFormula()}) and that sub-term's top-level term as the
     * original ({@link #getOriginalFormula()}).
     *
     * @author lanzinger
     */
    public static final class Entry implements SequentPrintFilterEntry {

        /**
         * The filtered formula, i.e., the formula at {@code pos}.
         */
        private final SequentFormula filtered;

        /**
         * The origin formula, i.e., the formula at {@code pos.getTopLevel()}.
         */
        private final SequentFormula original;

        private Entry(PosInOccurrence pos) {
            filtered = new SequentFormula(pos.subTerm());
            original = pos.sequentFormula();
        }

        @Override
        public SequentFormula getFilteredFormula() {
            return filtered;
        }

        @Override
        public SequentFormula getOriginalFormula() {
            return original;
        }

    }
}
