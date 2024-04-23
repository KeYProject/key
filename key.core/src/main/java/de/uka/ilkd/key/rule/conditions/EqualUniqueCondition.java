/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.op.Function;


public final class EqualUniqueCondition implements VariableCondition {
    private final TermSV t;
    private final TermSV t2;
    private final FormulaSV res;


    public EqualUniqueCondition(TermSV t, TermSV t2, FormulaSV res) {
        this.t = t;
        this.t2 = t2;
        this.res = res;
    }


    private static Term equalUnique(Term t1, Term t2, TermServices services) {
        if (!(t1.op() instanceof JFunction && t2.op() instanceof JFunction
                && ((Function) t1.op()).isUnique() && ((Function) t2.op()).isUnique())) {
            return null;
        } else if (t1.op() == t2.op()) {
            Term result = services.getTermBuilder().tt();
            for (int i = 0, n = t1.arity(); i < n; i++) {
                result = services.getTermBuilder().and(result,
                    services.getTermBuilder().equals(t1.sub(i), t2.sub(i)));
            }
            return result;
        } else {
            return services.getTermBuilder().ff();
        }
    }


    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate, MatchConditions mc,
            Services services) {
        SVInstantiations svInst = mc.getInstantiations();
        Term tInst = (Term) svInst.getInstantiation(t);
        Term t2Inst = (Term) svInst.getInstantiation(t2);
        Term resInst = (Term) svInst.getInstantiation(res);
        if (tInst == null || t2Inst == null) {
            return mc;
        }

        Term properResInst = equalUnique(tInst, t2Inst, services);
        if (properResInst == null) {
            return null;
        } else if (resInst == null) {
            svInst = svInst.add(res, properResInst, services);
            return mc.setInstantiations(svInst);
        } else if (resInst.equals(properResInst)) {
            return mc;
        } else {
            return null;
        }
    }


    @Override
    public String toString() {
        return "\\equalUnique (" + t + ", " + t2 + ", " + res + ")";
    }
}
