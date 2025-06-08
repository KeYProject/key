/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.VariableCondition;
import org.key_project.prover.rules.instantiation.MatchConditions;


public final class DropEffectlessElementariesCondition implements VariableCondition {
    private final UpdateSV u;
    private final SchemaVariable x;
    private final SchemaVariable result;

    public DropEffectlessElementariesCondition(UpdateSV u, SchemaVariable x, SchemaVariable x2) {
        this.u = u;
        this.x = x;
        this.result = x2;
    }


    private static JTerm dropEffectlessElementariesHelper(JTerm update,
            Set<LocationVariable> relevantVars, TermServices services) {
        if (update.op() instanceof ElementaryUpdate eu) {
            LocationVariable lhs = (LocationVariable) eu.lhs();
            if (relevantVars.contains(lhs)) {
                relevantVars.remove(lhs);
                // removed, see bug #1269 (MU, CS)
                // // updates of the form "x:=x" can be discarded (MU,CS)
                // if(lhs.equals(update.sub(0).op())) {
                // return TB.skip();
                // }
                return null;
            } else {
                return services.getTermBuilder().skip();
            }
        } else if (update.op() == UpdateJunctor.PARALLEL_UPDATE) {
            JTerm sub0 = update.sub(0);
            JTerm sub1 = update.sub(1);
            // first descend to the second sub-update to keep relevantVars in
            // good order
            JTerm newSub1 = dropEffectlessElementariesHelper(sub1, relevantVars, services);
            JTerm newSub0 = dropEffectlessElementariesHelper(sub0, relevantVars, services);
            if (newSub0 == null && newSub1 == null) {
                return null;
            } else {
                newSub0 = newSub0 == null ? sub0 : newSub0;
                newSub1 = newSub1 == null ? sub1 : newSub1;
                return services.getTermBuilder().parallel(newSub0, newSub1);
            }
        } else if (update.op() == UpdateApplication.UPDATE_APPLICATION) {
            JTerm sub0 = update.sub(0);
            JTerm sub1 = update.sub(1);
            JTerm newSub1 = dropEffectlessElementariesHelper(sub1, relevantVars, services);
            return newSub1 == null ? null : services.getTermBuilder().apply(sub0, newSub1, null);
        } else {
            return null;
        }
    }


    private static JTerm dropEffectlessElementaries(JTerm update, JTerm target,
            LogicServices p_services) {
        final Services services = (Services) p_services;
        TermProgramVariableCollector collector = services.getFactory().create(services);
        target.execPostOrder(collector);
        Set<LocationVariable> varsInTarget = collector.result();
        JTerm simplifiedUpdate = dropEffectlessElementariesHelper(update, varsInTarget, services);
        return simplifiedUpdate == null ? null
                : services.getTermBuilder().apply(simplifiedUpdate, target, null);
    }



    @Override
    public MatchConditions check(SchemaVariable var, SyntaxElement instCandidate,
            MatchConditions mc,
            LogicServices services) {
        SVInstantiations svInst =
            (SVInstantiations) mc.getInstantiations();
        JTerm uInst = (JTerm) svInst.getInstantiation(u);
        JTerm xInst = (JTerm) svInst.getInstantiation(x);
        JTerm resultInst = (JTerm) svInst.getInstantiation(result);
        if (uInst == null || xInst == null) {
            return mc;
        }

        JTerm properResultInst = dropEffectlessElementaries(uInst, xInst, services);
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
