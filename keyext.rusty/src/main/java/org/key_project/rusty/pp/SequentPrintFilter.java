/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.pp;

import org.key_project.prover.sequent.Sequent;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;


/**
 * Filter a given sequent to prepare it for the SequentPrinter class by adjusting constraints,
 * deleting formulas, etc.
 */
public abstract class SequentPrintFilter {
    /**
     * the original sequent
     */
    org.key_project.prover.sequent.Sequent originalSequent;

    /**
     * the antecedent of the filtered formula
     */
    ImmutableList<SequentPrintFilterEntry> antec = ImmutableSLList.nil();

    /**
     * the antecedent of the filtered formula
     */
    ImmutableList<SequentPrintFilterEntry> succ = ImmutableSLList.nil();

    /**
     * @return the original sequent
     */
    public org.key_project.prover.sequent.Sequent getOriginalSequent() {
        return originalSequent;
    }

    /**
     * filters the sequent according to filter type
     */
    protected abstract void filterSequent();

    /**
     * sets the (original) sequent of this filter
     *
     * @param s the sequent s is set to
     */
    public void setSequent(Sequent s) {
        originalSequent = s;
        antec = null;
        succ = null;
        filterSequent();
    }

    /**
     * Get the formulas of the filtered antecedent and the constraints to use for instantiating
     * metavariables when printing
     *
     * @return the filtered antecedent
     */
    public ImmutableList<SequentPrintFilterEntry> getFilteredAntec() {
        return antec;
    }

    /**
     * Get the formulas of the filtered succcedent and the constraints to use for instantiating
     * metavariables when printing
     *
     * @return the filtered succcedent
     */
    public ImmutableList<SequentPrintFilterEntry> getFilteredSucc() {
        return succ;
    }

    /**
     * converts the complete original sequent into antecedent/succendent lists of print filter
     * entries.
     */
    protected void filterIdentity() {
        antec = ImmutableSLList.nil();
        for (var sf : originalSequent.antecedent()) {
            antec = antec.append(
                new IdentitySequentPrintFilter.IdentityFilterEntry(sf));
        }

        succ = ImmutableSLList.nil();
        for (var sf : originalSequent.succedent()) {
            succ = succ.append(
                new IdentitySequentPrintFilter.IdentityFilterEntry(sf));
        }
    }
}
