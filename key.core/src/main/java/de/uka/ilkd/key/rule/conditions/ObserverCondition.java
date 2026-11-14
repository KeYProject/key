/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.conditions;


import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.TermSV;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.VariableCondition;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.instantiation.SVInstantiations;


/**
 * A variable condition for the taclet construct {@code \isObserver}, checking that a term schema
 * variable is instantiated with an observer function and that the heap argument of the observer is
 * the given heap term. If the heap schema variable is not yet instantiated, it is bound to the
 * observer's heap argument.
 *
 * @author Michael Kirsten
 */
public final class ObserverCondition implements VariableCondition {

    private final TermSV obs;
    private final TermSV heap;


    /**
     * Instantiates a new observer condition.
     *
     * @param obs the term schema variable which must be instantiated with an observer function
     *        application (an {@link IObserverFunction})
     * @param heap the term schema variable for the heap on which the observer is evaluated; it is
     *        automatically instantiated with the observer's heap argument if not yet instantiated
     */
    public ObserverCondition(TermSV obs, TermSV heap) {
        this.obs = obs;
        this.heap = heap;
    }


    @Override
    public MatchResultInfo check(SchemaVariable var, SyntaxElement instCandidate,
            MatchResultInfo mc,
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
