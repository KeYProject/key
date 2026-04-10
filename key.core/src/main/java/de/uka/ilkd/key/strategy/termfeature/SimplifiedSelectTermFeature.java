/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termfeature.BinaryTermFeature;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;

public final class SimplifiedSelectTermFeature extends BinaryTermFeature {

    private final HeapLDT heapLDT;
    private final PrimitiveHeapTermFeature primitiveHeapTermFeature;

    private SimplifiedSelectTermFeature(HeapLDT heapLDT) {
        this.heapLDT = heapLDT;
        this.primitiveHeapTermFeature = PrimitiveHeapTermFeature.create(heapLDT);
    }

    public static TermFeature create(HeapLDT heapLDT) {
        return new SimplifiedSelectTermFeature(heapLDT);
    }

    @Override
    protected boolean filter(Term term, MutableState mState, LogicServices services) {
        var t = (JTerm) term;
        boolean isSelectOp = heapLDT.getSortOfSelect(t.op()) != null;
        return // either the operator is not a select operator
        !isSelectOp ||
        // or the heap term of the select operator is the base heap
        // or another primitive heap variable
                primitiveHeapTermFeature.filter(t.sub(0), mState, services) ||
                // or the heap term of the select operator is an anon heap symbol
                // (for instance an anonHeap function)
                (t.sub(0).op() instanceof Function && t.sub(0).op().arity() == 0
                        && t.sub(0).hasLabels()
                        && t.sub(0).containsLabel(ParameterlessTermLabel.ANON_HEAP_LABEL));

    }
}
