/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.rule;

import java.util.List;

import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.AbstractLoopInvariantRule;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.speclang.LoopSpecification;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (7/28/25)
 */
public class InfFlowLoopInvariantBuiltInRuleApp<T extends AbstractLoopInvariantRule>
        extends LoopInvariantBuiltInRuleApp<T> {

    private IFProofObligationVars infFlowVars;

    protected InfFlowLoopInvariantBuiltInRuleApp(T rule, PosInOccurrence pio,
            @Nullable ImmutableList<PosInOccurrence> ifInsts, @Nullable LoopSpecification inv,
            @Nullable List<LocationVariable> heapContext, TermServices services) {
        super(rule, pio, ifInsts, inv, heapContext, services);
    }

    protected InfFlowLoopInvariantBuiltInRuleApp(T rule, PosInOccurrence pio, LoopSpecification inv,
            TermServices services) {
        super(rule, pio, inv, services);
    }

    public InfFlowLoopInvariantBuiltInRuleApp(T rule, PosInOccurrence pos, TermServices services) {
        super(rule, pos, services);
    }

    public void setInformationFlowProofObligationVars(IFProofObligationVars vars) {
        this.infFlowVars = vars;
    }

    public IFProofObligationVars getInformationFlowProofObligationVars() {
        return infFlowVars;
    }

}
