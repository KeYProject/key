/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.axiom_abstraction.signanalysis;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;

import org.key_project.logic.Name;

/**
 * The Leq element of the sign lattice, representing all negative numbers and zero.
 *
 * @author Dominic Scheurer
 */
public class Leq extends SignAnalysisDomainElem {

    private static final Leq INSTANCE = new Leq();

    private Leq() {}

    public static Leq getInstance() {
        return INSTANCE;
    }

    @Override
    public Name name() {
        return new Name("leq");
    }

    @Override
    public JTerm getDefiningAxiom(JTerm varOrConst, Services services) {
        TermBuilder tb = services.getTermBuilder();
        return services.getTermBuilder().leq(varOrConst, tb.zero());
    }

    @Override
    public String toParseableString(Services services) {
        return toString();
    }

}
