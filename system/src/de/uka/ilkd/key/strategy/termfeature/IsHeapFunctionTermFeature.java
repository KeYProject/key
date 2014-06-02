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
            return op.arity() == 0 &&
                   op.sort() == heapLDT.targetSort();
        } else {
            return false;
        }
    }
}
