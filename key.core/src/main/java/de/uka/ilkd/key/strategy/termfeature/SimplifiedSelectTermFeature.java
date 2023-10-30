/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.Function;


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
    protected boolean filter(Term t, Services services) {
        boolean isSelectOp = heapLDT.getSortOfSelect(t.op()) != null;
        return // either the operator is not a select operator
        !isSelectOp ||
        // or the heap term of the select operator is the base heap
        // or another primitive heap variable
                primitiveHeapTermFeature.filter(t.sub(0), services) ||
                // or the heap term of the select operator is an anon heap symbol
                // (for instance an anonHeap function)
                (t.sub(0).op() instanceof Function && t.sub(0).op().arity() == 0
                        && t.sub(0).hasLabels()
                        && t.sub(0).containsLabel(ParameterlessTermLabel.ANON_HEAP_LABEL));

    }
}
