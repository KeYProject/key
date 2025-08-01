/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.wd;

import java.util.List;
import java.util.function.Consumer;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.macros.WellDefinednessMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.WhileInvariantRule;
import de.uka.ilkd.key.rule.WhileInvariantRule.*;
import de.uka.ilkd.key.speclang.LoopSpecification;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import com.google.auto.service.AutoService;


@AutoService(WhileInvariantHook.class)
public class WdWhileInvariantRuleHook implements WhileInvariantRule.WhileInvariantHook {
    @Override
    public Consumer<Goal> createGoal(RuleApp ruleApp, Instantiation inst,
            Services services, LoopInvariantBuiltInRuleApp loopRuleApp,
            JavaBlock guardJb, ImmutableSet<LocationVariable> localIns,
            ImmutableSet<LocationVariable> localOuts, ImmutableList<AnonUpdateData> anonUpdateDatas,
            JTerm anonUpdate, List<LocationVariable> heapContext,
            JTerm anonHeap, JTerm localAnonUpdate) {
        if (WellDefinednessCheck.isOn()) {
            return setupWdGoal(inst.inv, inst.u, inst.selfTerm, heapContext.getFirst(), anonHeap,
                localAnonUpdate, localIns, ruleApp.posInOccurrence(), services);
        }

        return null; // wd is off
    }

    private Consumer<Goal> setupWdGoal(final LoopSpecification inv, final JTerm update,
            final JTerm selfTerm, final LocationVariable heap, final JTerm anonHeap,
            final JTerm localAnonUpdate, final ImmutableSet<LocationVariable> localIns,
            PosInOccurrence pio, Services services) {
        return (goal) -> {
            goal.setBranchLabel(WellDefinednessMacro.WD_BRANCH);
            final LoopWellDefinedness lwd = new LoopWellDefinedness(inv, localIns, services);
            final LocationVariable self;
            if (selfTerm != null && selfTerm.op() instanceof LocationVariable) {
                self = (LocationVariable) selfTerm.op();
            } else {
                self = null;
            }
            services.getSpecificationRepository().addWdStatement(lwd);
            final SequentFormula wdInv =
                lwd.generateSequent(self, heap, anonHeap, localIns, update, localAnonUpdate,
                    services);
            goal.changeFormula(wdInv, pio);
        };
    }
}
