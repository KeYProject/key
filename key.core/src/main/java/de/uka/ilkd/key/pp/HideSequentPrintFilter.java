/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.pp;

import java.util.Iterator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.pp.IdentitySequentPrintFilter.IdentityFilterEntry;

import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;

/**
 * This filter takes a search string and yields a sequent containing only sequent formulas that
 * match the search.
 *
 * @author jschiffl
 */
@NullMarked
public class HideSequentPrintFilter extends SearchSequentPrintFilter {

    /**
     *
     * @param lp the logic printer in use
     * @param regex should the search be treated as regex?
     */
    public HideSequentPrintFilter(SequentViewLogicPrinter lp, boolean regex) {
        super(lp);
        this.regex = regex;
    }

    @Override
    /**
     * Filters the formatted formulas of the sequent, keeping those matching the search pattern.
     * <p>
     * The antecedent and succedent filter lists are re-initialized after the early returns below;
     * the dereferences of the (nullable) list fields are suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    protected void filterSequent() {
        Iterator<SequentFormula> it;

        if (antec != null) {
            // Result has already been computed. No need to recompute.
            return;
        }

        if (searchString == null || searchString.length() < 3) {
            filterIdentity();
            return;
        }

        Pattern p = createPattern();
        if (p == null) {
            filterIdentity();
            return;
        }

        antec = ImmutableList.nil();
        it = originalSequent.antecedent().iterator();
        while (it.hasNext()) {
            SequentFormula sf = it.next();
            lp.reset();
            lp.printConstrainedFormula(sf);
            String formString = lp.result();
            Matcher m = p.matcher(formString.replace("\u00A0", "\u0020"));
            if (m.find()) {
                antec = antec.append(new IdentityFilterEntry(sf));
            }
        }

        succ = ImmutableList.nil();
        it = originalSequent.succedent().iterator();
        while (it.hasNext()) {
            SequentFormula sf = it.next();
            lp.reset();
            lp.printConstrainedFormula(sf);
            String formString = lp.result();
            Matcher m = p.matcher(formString.replace("\u00A0", "\u0020"));
            if (m.find()) {
                succ = succ.append(new IdentityFilterEntry(sf));
            }
        }
    }
}
