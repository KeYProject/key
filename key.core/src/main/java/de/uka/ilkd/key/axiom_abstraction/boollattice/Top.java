/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.axiom_abstraction.boollattice;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;

import org.key_project.logic.Name;

/**
 * The Top element of the boolean lattice, representing all booleans (i.e., true and false).
 *
 * @author Dominic Scheurer
 */
public class Top extends BooleanDomainElem {

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
    public JTerm getDefiningAxiom(JTerm varOrConst, Services services) {
        TermBuilder tb = services.getTermBuilder();
        return tb.tt();
    }

    @Override
    public String toParseableString(Services services) {
        return toString();
    }

}
