/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.axiom_abstraction.boollattice;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LogicVariable;

import org.key_project.logic.Name;

/**
 * The Bottom element of the boolean lattice, representing no boolean at all.
 *
 * @author Dominic Scheurer
 */
public class Bottom extends BooleanDomainElem {

    private static final Bottom INSTANCE = new Bottom();

    private Bottom() {}

    public static Bottom getInstance() {
        return INSTANCE;
    }

    @Override
    public Name name() {
        return new Name("bottom");
    }

    @Override
    public Term getDefiningAxiom(Term varOrConst, Services services) {
        TermBuilder tb = services.getTermBuilder();

        final Name freshVarName = new Name(tb.newName(varOrConst.sort()));
        LogicVariable freshVar = new LogicVariable(freshVarName, varOrConst.sort());
        services.getNamespaces().variables().add(freshVar);

        Term axiom = tb.equals(varOrConst, tb.var(freshVar));
        axiom = tb.not(axiom);
        axiom = tb.all(freshVar, axiom);

        return axiom;
    }

    @Override
    public String toParseableString(Services services) {
        return toString();
    }

}
