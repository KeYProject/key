/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.rule;

import java.util.List;

import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.LoopSpecification;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (7/28/25)
 */
public class InfFlowLoopInvariantBuiltInRuleApp
        extends LoopInvariantBuiltInRuleApp<InfFlowWhileInvariantRule> {

    private @Nullable IFProofObligationVars infFlowVars;

    protected InfFlowLoopInvariantBuiltInRuleApp(InfFlowWhileInvariantRule rule,
            PosInOccurrence pio,
            @Nullable ImmutableList<PosInOccurrence> ifInsts, @Nullable LoopSpecification inv,
            @Nullable List<LocationVariable> heapContext, TermServices services) {
        super(rule, pio, ifInsts, inv, heapContext, services);
    }

    protected InfFlowLoopInvariantBuiltInRuleApp(InfFlowWhileInvariantRule rule,
            PosInOccurrence pio, LoopSpecification inv,
            TermServices services) {
        super(rule, pio, inv, services);
    }

    public InfFlowLoopInvariantBuiltInRuleApp(InfFlowWhileInvariantRule rule, PosInOccurrence pos,
            TermServices services) {
        super(rule, pos, services);
    }

    @Override
    public InfFlowLoopInvariantBuiltInRuleApp tryToInstantiate(Goal goal) {
        if (getSpec() != null) {
            return this;
        }
        final Services services = goal.proof().getServices();
        LoopSpecification inv = retrieveLoopInvariantFromSpecification(services);
        var m = ((JModality) programTerm().op()).<JModality.JavaModalityKind>kind();
        return new InfFlowLoopInvariantBuiltInRuleApp(builtInRule, pio, ifInsts, inv,
            HeapContext.getModifiableHeaps(services, m.transaction()), services);
    }

    @Override
    public InfFlowLoopInvariantBuiltInRuleApp replacePos(PosInOccurrence newPos) {
        return new InfFlowLoopInvariantBuiltInRuleApp(builtInRule, newPos, ifInsts, spec,
            heapContext, services);
    }

    @Override
    public InfFlowLoopInvariantBuiltInRuleApp setAssumesInsts(
            ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
    }

    @Override
    public InfFlowLoopInvariantBuiltInRuleApp setLoopInvariant(LoopSpecification inv) {
        if (this.loop == inv.getLoop()) {
            this.spec = inv;
        }
        return new InfFlowLoopInvariantBuiltInRuleApp(builtInRule, pio, ifInsts, inv, heapContext,
            services);
    }

    public void setInformationFlowProofObligationVars(IFProofObligationVars vars) {
        this.infFlowVars = vars;
    }

    public IFProofObligationVars getInformationFlowProofObligationVars() {
        return infFlowVars;
    }
}
