/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.varcond;

import java.util.Set;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.ElementaryUpdate;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.logic.op.UpdateApplication;
import org.key_project.rusty.logic.op.UpdateJunctor;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.logic.op.sv.UpdateSV;
import org.key_project.rusty.proof.TermProgramVariableCollector;
import org.key_project.rusty.rule.MatchConditions;
import org.key_project.rusty.rule.VariableCondition;
import org.key_project.rusty.rule.inst.SVInstantiations;

public final class DropEffectlessElementariesCondition implements VariableCondition {
    private final UpdateSV u;
    private final SchemaVariable x;
    private final SchemaVariable result;

    public DropEffectlessElementariesCondition(UpdateSV u, SchemaVariable x, SchemaVariable x2) {
        this.u = u;
        this.x = x;
        this.result = x2;
    }


    private static Term dropEffectlessElementariesHelper(Term update,
            Set<ProgramVariable> relevantVars, Services services) {
        if (update.op() instanceof ElementaryUpdate eu) {
            var lhs = (ProgramVariable) eu.lhs();
            if (relevantVars.contains(lhs)) {
                relevantVars.remove(lhs);
                return null;
            } else {
                return services.getTermBuilder().skip();
            }
        } else if (update.op() == UpdateJunctor.PARALLEL_UPDATE) {
            Term sub0 = update.sub(0);
            Term sub1 = update.sub(1);
            // first descend to the second sub-update to keep relevantVars in
            // good order
            Term newSub1 = dropEffectlessElementariesHelper(sub1, relevantVars, services);
            Term newSub0 = dropEffectlessElementariesHelper(sub0, relevantVars, services);
            if (newSub0 == null && newSub1 == null) {
                return null;
            } else {
                newSub0 = newSub0 == null ? sub0 : newSub0;
                newSub1 = newSub1 == null ? sub1 : newSub1;
                return services.getTermBuilder().parallel(newSub0, newSub1);
            }
        } else if (update.op() == UpdateApplication.UPDATE_APPLICATION) {
            Term sub0 = update.sub(0);
            Term sub1 = update.sub(1);
            Term newSub1 = dropEffectlessElementariesHelper(sub1, relevantVars, services);
            return newSub1 == null ? null : services.getTermBuilder().apply(sub0, newSub1);
        } else {
            return null;
        }
    }


    private static Term dropEffectlessElementaries(Term update, Term target, Services services) {
        TermProgramVariableCollector collector = new TermProgramVariableCollector(services);
        target.execPostOrder(collector);
        Set<ProgramVariable> varsInTarget = collector.result();
        Term simplifiedUpdate = dropEffectlessElementariesHelper(update, varsInTarget, services);
        return simplifiedUpdate == null ? null
                : services.getTermBuilder().apply(simplifiedUpdate, target);
    }



    @Override
    public MatchConditions check(SchemaVariable var, SyntaxElement instCandidate,
            MatchConditions mc,
            Services services) {
        SVInstantiations svInst = mc.getInstantiations();
        Term uInst = (Term) svInst.getInstantiation(u);
        Term xInst = (Term) svInst.getInstantiation(x);
        Term resultInst = (Term) svInst.getInstantiation(result);
        if (uInst == null || xInst == null) {
            return mc;
        }

        Term properResultInst = dropEffectlessElementaries(uInst, xInst, services);
        if (properResultInst == null) {
            return null;
        } else if (resultInst == null) {
            svInst = svInst.add(result, properResultInst, services);
            return mc.setInstantiations(svInst);
        } else if (resultInst.equals(properResultInst)) {
            return mc;
        } else {
            return null;
        }
    }


    @Override
    public String toString() {
        return "\\dropEffectlessElementaries(" + u + ", " + x + ", " + result + ")";
    }
}
