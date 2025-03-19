/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.axiom_abstraction.signanalysis;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

import org.key_project.logic.Name;

/**
 * The Top element of the sign lattice, representing all integers.
 *
 * @author Dominic Scheurer
 */
public class Top extends SignAnalysisDomainElem {

    private static final Top INSTANCE = new Top();

    private Top() {}

    public static Top getInstance() {
        return INSTANCE;
    }

    @Override
    public Name name() {
        return new Name("top");
    }

    @Override
    public Term getDefiningAxiom(Term varOrConst, Services services) {
        TermBuilder tb = services.getTermBuilder();
        return tb.inInt(varOrConst);
    }

    @Override
    public String toParseableString(Services services) {
        return toString();
    }

}
