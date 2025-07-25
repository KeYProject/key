/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.axiom_abstraction.signanalysis;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LogicVariable;

import org.key_project.logic.Name;

/**
 * The Bottom element of the sign lattice, representing no number at all.
 *
 * @author Dominic Scheurer
 */
public class Bottom extends SignAnalysisDomainElem {

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
    public JTerm getDefiningAxiom(JTerm varOrConst, Services services) {
        TermBuilder tb = services.getTermBuilder();

        final Name freshVarName = new Name(tb.newName(varOrConst.sort()));
        LogicVariable freshVar = new LogicVariable(freshVarName, varOrConst.sort());
        services.getNamespaces().variables().add(freshVar);

        JTerm axiom = tb.equals(varOrConst, tb.var(freshVar));
        axiom = tb.not(axiom);
        axiom = tb.all(freshVar, axiom);

        return axiom;
    }

    @Override
    public String toParseableString(Services services) {
        return toString();
    }

}
