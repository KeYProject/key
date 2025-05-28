/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;


import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.TermSV;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.VariableCondition;
import org.key_project.prover.rules.instantiation.MatchConditions;
import org.key_project.prover.rules.instantiation.SVInstantiations;


public final class ObserverCondition implements VariableCondition {

    private final TermSV obs;
    private final TermSV heap;


    public ObserverCondition(TermSV obs, TermSV heap) {
        this.obs = obs;
        this.heap = heap;
    }


    @Override
    public MatchConditions check(SchemaVariable var, SyntaxElement instCandidate,
            MatchConditions mc,
            LogicServices services) {
        SVInstantiations svInst = mc.getInstantiations();
        final JTerm obsInst = (JTerm) svInst.getInstantiation(obs);

        if (obsInst == null) {
            return mc;
        } else if (!(obsInst.op() instanceof IObserverFunction)) {
            return null;
        }

        final JTerm heapInst = (JTerm) svInst.getInstantiation(heap);
        final JTerm properHeapInst = obsInst.sub(0);
        if (heapInst == null) {
            svInst = ((de.uka.ilkd.key.rule.inst.SVInstantiations) svInst).add(heap, properHeapInst,
                services);
            return mc.setInstantiations(svInst);
        } else if (heapInst.equals(properHeapInst)) {
            return mc;
        } else {
            return null;
        }
    }


    @Override
    public String toString() {
        return "\\isObserver (" + obs + ", " + heap + ")";
    }
}
