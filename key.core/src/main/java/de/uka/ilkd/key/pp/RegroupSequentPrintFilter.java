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
 * @author jschiffl This filter takes a search string and regroups the sequent so that the sequent
 *         formulas matching the search are grouped around the sequent arrow, so that they can be
 *         viewed together.
 */

@NullMarked
public class RegroupSequentPrintFilter extends SearchSequentPrintFilter {

    /**
     *
     * @param lp the logic printer in use
     * @param regex should the search be treated as a regular expression?
     */
    public RegroupSequentPrintFilter(SequentViewLogicPrinter lp, boolean regex) {
        super(lp);
        this.regex = regex;
    }

    /**
     * Regroups the formulas of the sequent into the antecedent and succedent lists according to
     * the configured search string or regular expression.
     * <p>
     * The antecedent and succedent filter lists are re-initialized before they are appended to or
     * prepended below; the dereferences of the (nullable) list fields are suppressed with a scoped
     * key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    @Override
    protected void filterSequent() {

        Iterator<SequentFormula> it;

        if (searchString == null || searchString.length() < 3) {
            filterIdentity();
            return;
        }

        Pattern p = createPattern();
        if (p == null) {
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
            } else {
                antec = antec.prepend(new IdentityFilterEntry(sf));
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
                succ = succ.prepend(new IdentityFilterEntry(sf));
            } else {
                succ = succ.append(new IdentityFilterEntry(sf));
            }
        }
    }
}
