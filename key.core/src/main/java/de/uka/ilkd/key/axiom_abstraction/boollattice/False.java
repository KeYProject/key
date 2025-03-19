/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.axiom_abstraction.boollattice;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

import org.key_project.logic.Name;

/**
 * The False element of the boolean lattice, representing exactly the boolean false.
 *
 * @author Dominic Scheurer
 */
public class False extends BooleanDomainElem {

    private static final False INSTANCE = new False();

    private False() {}

    public static False getInstance() {
        return INSTANCE;
    }

    @Override
    public Name name() {
        return new Name("false");
    }

    @Override
    public Term getDefiningAxiom(Term varOrConst, Services services) {
        TermBuilder tb = services.getTermBuilder();
        return tb.equals(varOrConst, tb.ff());
    }

    @Override
    public String toParseableString(Services services) {
        return toString();
    }

}
