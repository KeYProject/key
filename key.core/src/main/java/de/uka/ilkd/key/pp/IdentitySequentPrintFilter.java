/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.logic.SequentFormula;

import org.key_project.util.collection.ImmutableList;

/**
 * Identity Filter not doing anything
 */
public class IdentitySequentPrintFilter extends SequentPrintFilter {

    /**
     * filters the sequent, creating SequentPrintFilterEntries from the sequent formulae.
     */
    protected void filterSequent() {
        if (antec != null) {
            return;
        }
        filterIdentity();
    }

    /**
     *
     * @param sequentFormula the formula to filter
     * @return the FilterEntry from the formula
     */
    protected SequentPrintFilterEntry filterFormula(SequentFormula sequentFormula) {
        return new IdentityFilterEntry(sequentFormula);
    }

    /**
     * Get the formulas of the filtered antecedent and the constraints to use for instantiating
     * metavariables when printing
     *
     * @return the filtered antecedent
     */
    public ImmutableList<SequentPrintFilterEntry> getFilteredAntec() {
        filterSequent();
        return antec;
    }

    /**
     * Get the formulas of the filtered succcedent and the constraints to use for instantiating
     * metavariables when printing
     *
     * @return the filtered succcedent
     */
    public ImmutableList<SequentPrintFilterEntry> getFilteredSucc() {
        filterSequent();
        return succ;
    }

    /**
     * A filter entry, representing one sequent formula.
     */
    public static class IdentityFilterEntry implements SequentPrintFilterEntry {
        /**
         * the original Formula being filtered
         */
        final SequentFormula originalFormula;

        /**
         * constructor
         *
         * @param originalFormula the original formula to be filtered
         */
        IdentityFilterEntry(SequentFormula originalFormula) {
            this.originalFormula = originalFormula;
        }

        /**
         * Formula to display
         *
         * @return the original formula
         */
        public SequentFormula getFilteredFormula() {
            return originalFormula;
        }

        /**
         * Original formula from sequent
         *
         * @return the original formula
         */
        public SequentFormula getOriginalFormula() {
            return originalFormula;
        }

    }
}
