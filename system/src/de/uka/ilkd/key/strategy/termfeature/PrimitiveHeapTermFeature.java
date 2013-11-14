// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.label.AnonHeapTermLabel;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import java.util.Iterator;


public final class PrimitiveHeapTermFeature extends BinaryTermFeature {

    private final HeapLDT heapLDT;

    private PrimitiveHeapTermFeature(HeapLDT heapLDT) {
        this.heapLDT = heapLDT;
    }

    public static PrimitiveHeapTermFeature create(HeapLDT heapLDT) {
        return new PrimitiveHeapTermFeature(heapLDT);
    }

    @Override
    protected boolean filter(Term t) {
        // t.op() is the base heap or another primitive heap variable
        boolean isPrimitive = false;
        Iterator<LocationVariable> it = heapLDT.getAllHeaps().iterator();
        while (!isPrimitive && it.hasNext()) {
            isPrimitive = (it.next() == t.op());
        }
        return isPrimitive;
    }
}
