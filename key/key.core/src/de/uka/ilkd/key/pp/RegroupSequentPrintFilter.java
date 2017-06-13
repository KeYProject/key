// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.pp;

import java.io.IOException;
import java.util.Iterator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter.IdentityFilterEntry;

/**
 * @author jschiffl
 *         This filter takes a search string and regroups the sequent
 *         so that the sequent formulas matching the search are grouped around
 *         the sequent arrow, so that they can be viewed together.
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

        antec = ImmutableSLList.<SequentPrintFilterEntry>nil();
        it = originalSequent.antecedent().iterator();
        while (it.hasNext()) {
            SequentFormula sf = it.next();
            try {
                lp.reset();
                lp.printConstrainedFormula(sf);
            } catch (IOException e) {
                e.printStackTrace();
            }
            String formString = lp.toString();
            Matcher m = p.matcher(formString.replace("\u00A0", "\u0020"));
            if (m.find()) {
                antec = antec.append(new IdentityFilterEntry(sf));
            } else {
                antec = antec.prepend(new IdentityFilterEntry(sf));
            }
        }

        succ = ImmutableSLList.<SequentPrintFilterEntry>nil();
        it = originalSequent.succedent().iterator();
        while (it.hasNext()) {
            SequentFormula sf = it.next();
            try {
                lp.reset();
                lp.printConstrainedFormula(sf);
            } catch (IOException e) {
                e.printStackTrace();
            }
            String formString = lp.toString();
            Matcher m = p.matcher(formString.replace("\u00A0", "\u0020"));
            if (m.find()) {
                succ = succ.prepend(new IdentityFilterEntry(sf));
            } else {
                succ = succ.append(new IdentityFilterEntry(sf));
            }
        }
    }
}
