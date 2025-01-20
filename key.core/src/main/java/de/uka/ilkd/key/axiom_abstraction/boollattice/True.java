/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.axiom_abstraction.boollattice;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

import org.key_project.logic.Name;

/**
 * The True element of the boolean lattice, representing exactly the boolean true.
 *
 * @author Dominic Scheurer
 */
public class True extends BooleanDomainElem {

    private static final True INSTANCE = new True();

    private True() {}

    public static True getInstance() {
        return INSTANCE;
    }

    @Override
    public Name name() {
        return new Name("true");
    }

    @Override
    public Term getDefiningAxiom(Term varOrConst, Services services) {
        TermBuilder tb = services.getTermBuilder();
        return tb.equals(varOrConst, tb.tt());
    }

    @Override
    public String toParseableString(Services services) {
        return toString();
    }

}
