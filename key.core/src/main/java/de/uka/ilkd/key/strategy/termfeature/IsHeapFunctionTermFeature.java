/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;


public final class IsHeapFunctionTermFeature extends BinaryTermFeature {

    private final HeapLDT heapLDT;

    private IsHeapFunctionTermFeature(HeapLDT heapLDT) {
        this.heapLDT = heapLDT;
    }

    public static IsHeapFunctionTermFeature create(HeapLDT heapLDT) {
        return new IsHeapFunctionTermFeature(heapLDT);
    }

    @Override
    protected boolean filter(Term t, Services services) {
        if (t.op() instanceof Function) {
            Function op = t.op(Function.class);
            return op.arity() == 0 && op.sort() == heapLDT.targetSort();
        } else {
            return false;
        }
    }
}
