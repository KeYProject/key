/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.WaryClashFreeSubst;


public final class WarySubstOp extends SubstOp {

    /**
     * the wary substitution operator {var<-term}'. {x<-d}'A(x) means replace all free occurrences
     * of variable x in A with d, however without replacing x with a non-rigid A below modalities
     */
    public static final SubstOp SUBST = new WarySubstOp(new Name("subst"));


    private WarySubstOp(Name name) {
        super(name);
    }


    @Override
    public Term apply(Term term, TermBuilder tb) {
        QuantifiableVariable v = term.varsBoundHere(1).get(0);
        WaryClashFreeSubst cfSubst = new WaryClashFreeSubst(v, term.sub(0), tb);
        return cfSubst.apply(term.sub(1));
    }
}
