/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.axiom_abstraction.signanalysis;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;

import org.key_project.logic.Name;

/**
 * The Geq element of the sign lattice, representing all positive integers and zero.
 *
 * @author Dominic Scheurer
 */
public class Geq extends SignAnalysisDomainElem {

    private static final Geq INSTANCE = new Geq();

    private Geq() {}

    public static Geq getInstance() {
        return INSTANCE;
    }

    @Override
    public Name name() {
        return new Name("geq");
    }

    @Override
    public JTerm getDefiningAxiom(JTerm varOrConst, Services services) {
        TermBuilder tb = services.getTermBuilder();
        return services.getTermBuilder().geq(varOrConst, tb.zero());
    }

    @Override
    public String toParseableString(Services services) {
        return toString();
    }

}
