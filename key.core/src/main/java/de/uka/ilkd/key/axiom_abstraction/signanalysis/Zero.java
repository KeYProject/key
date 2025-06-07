/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.axiom_abstraction.signanalysis;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;

import org.key_project.logic.Name;

/**
 * The Zero element of the sign lattice, representing only the number 0.
 *
 * @author Dominic Scheurer
 */
public class Zero extends SignAnalysisDomainElem {

    private static final Zero INSTANCE = new Zero();

    private Zero() {}

    public static Zero getInstance() {
        return INSTANCE;
    }

    @Override
    public Name name() {
        return new Name("zero");
    }

    @Override
    public JTerm getDefiningAxiom(JTerm varOrConst, Services services) {
        TermBuilder tb = services.getTermBuilder();
        return services.getTermBuilder().equals(varOrConst, tb.zero());
    }

    @Override
    public String toParseableString(Services services) {
        return toString();
    }

}
