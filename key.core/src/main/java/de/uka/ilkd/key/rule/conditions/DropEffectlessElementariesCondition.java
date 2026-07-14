/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.BoundedProgramVariableCollector;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.VariableCondition;
import org.key_project.prover.rules.instantiation.MatchResultInfo;


public final class DropEffectlessElementariesCondition implements VariableCondition {
    private final UpdateSV u;
    private final SchemaVariable x;
    private final SchemaVariable result;

    public DropEffectlessElementariesCondition(UpdateSV u, SchemaVariable x, SchemaVariable x2) {
        this.u = u;
        this.x = x;
        this.result = x2;
    }


    static JTerm dropEffectlessElementariesHelper(JTerm update,
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
        return dropEffectlessElementariesTargeted(update, target, services);
    }

    /**
     * The helper only ever queries {@code relevantVars} with the update's
     * LHS variables, so we only need to know which of <em>those</em> occur in {@code target}.
     * Collecting just the update's LHS variables and searching the target for them -- with early
     * termination once all are found -- avoids the full program walk that made symbolic execution
     * quadratic (each update-simplification step re-walked the whole remaining program).
     */
    static JTerm dropEffectlessElementariesTargeted(JTerm update, JTerm target,
            Services services) {
        final Set<LocationVariable> updateVars = new LinkedHashSet<>();
        collectUpdateLhsVars(update, updateVars);

        final Set<LocationVariable> relevantVars = new LinkedHashSet<>();
        searchTerm(target, updateVars, relevantVars, services);

        JTerm simplifiedUpdate = dropEffectlessElementariesHelper(update, relevantVars, services);
        return simplifiedUpdate == null ? null
                : services.getTermBuilder().apply(simplifiedUpdate, target, null);
    }

    /**
     * Collects the LHS variables of the elementary updates that {@link
     * #dropEffectlessElementariesHelper} can reach, mirroring its traversal exactly (both sides of
     * a
     * parallel update; only the inner update of an update application).
     */
    private static void collectUpdateLhsVars(JTerm update, Set<LocationVariable> out) {
        final Operator op = update.op();
        if (op instanceof ElementaryUpdate eu) {
            out.add((LocationVariable) eu.lhs());
        } else if (op == UpdateJunctor.PARALLEL_UPDATE) {
            collectUpdateLhsVars(update.sub(0), out);
            collectUpdateLhsVars(update.sub(1), out);
        } else if (op == UpdateApplication.UPDATE_APPLICATION) {
            collectUpdateLhsVars(update.sub(1), out);
        }
    }

    /**
     * Records in {@code found} those variables of {@code interested} that occur in {@code term} --
     * either as a term operator, or inside a non-empty modality's Java program. The program part is
     * delegated to {@link BoundedProgramVariableCollector} so that loop invariants and
     * block/loop/merge contracts are covered exactly as by {@link
     * de.uka.ilkd.key.java.visitor.ProgramVariableCollector}, and so that the (only potentially
     * large) program walk stops as soon as all interested variables are found. The recursion itself
     * descends only until {@code found} already covers {@code interested}.
     */
    private static void searchTerm(JTerm term, Set<LocationVariable> interested,
            Set<LocationVariable> found, Services services) {
        if (found.size() == interested.size()) {
            return;
        }
        final Operator op = term.op();
        if (op instanceof LocationVariable lv && interested.contains(lv)) {
            found.add(lv);
        } else if (op instanceof JModality mod && !mod.programBlock().isEmpty()) {
            final BoundedProgramVariableCollector pvc = new BoundedProgramVariableCollector(
                mod.programBlock().program(), services, interested);
            pvc.start();
            for (LocationVariable v : interested) {
                if (pvc.result().contains(v)) {
                    found.add(v);
                }
            }
        }
        for (int i = 0, n = term.arity(); i < n; i++) {
            searchTerm(term.sub(i), interested, found, services);
        }
    }



    @Override
    public MatchResultInfo check(SchemaVariable var, SyntaxElement instCandidate,
            MatchResultInfo mc,
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
