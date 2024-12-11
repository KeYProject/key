/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.strategy.feature.MutableState;

import org.key_project.logic.Term;


public final class PrimitiveHeapTermFeature extends BinaryTermFeature {

    private final HeapLDT heapLDT;

    private PrimitiveHeapTermFeature(HeapLDT heapLDT) {
        this.heapLDT = heapLDT;
    }

    public static PrimitiveHeapTermFeature create(HeapLDT heapLDT) {
        return new PrimitiveHeapTermFeature(heapLDT);
    }

    @Override
    protected boolean filter(Term t, MutableState mState, Services services) {
        // t.op() is the base heap or another primitive heap variable
        boolean isPrimitive = false;
        Iterator<LocationVariable> it = heapLDT.getAllHeaps().iterator();
        while (!isPrimitive && it.hasNext()) {
            isPrimitive = (it.next() == t.op());
        }
        // the location variables which are created in the block contract rule
        // also need to be classified primitive
        isPrimitive = isPrimitive || (t.op() instanceof LocationVariable);
        return isPrimitive;
    }
}
