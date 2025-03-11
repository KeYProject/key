/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

import java.util.Iterator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter.IdentityFilterEntry;

import org.key_project.util.collection.ImmutableSLList;

/**
 * @author jschiffl This filter takes a search string and regroups the sequent so that the sequent
 *         formulas matching the search are grouped around the sequent arrow, so that they can be
 *         viewed together.
 */

public class RegroupSequentPrintFilter extends SearchSequentPrintFilter {

    /**
     *
     * @param lp the logic printer in use
     * @param regex should the search be treated as a regular expression?
     */
    public RegroupSequentPrintFilter(SequentViewLogicPrinter lp, boolean regex) {
        this.lp = lp;
        this.regex = regex;
    }

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

        antec = ImmutableSLList.nil();
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

        succ = ImmutableSLList.nil();
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
