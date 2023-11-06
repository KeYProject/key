/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.axiom_abstraction.signanalysis;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

/**
 * The Pos element of the sign lattice, representing all strictly positive numbers.
 *
 * @author Dominic Scheurer
 */
public class Pos extends SignAnalysisDomainElem {

    private static final Pos INSTANCE = new Pos();

    private Pos() {}

    public static Pos getInstance() {
        return INSTANCE;
    }

    @Override
    public Name name() {
        return new Name("pos");
    }

    @Override
    public Term getDefiningAxiom(Term varOrConst, Services services) {
        TermBuilder tb = services.getTermBuilder();
        return services.getTermBuilder().gt(varOrConst, tb.zero());
    }

    @Override
    public String toParseableString(Services services) {
        return toString();
    }

}
