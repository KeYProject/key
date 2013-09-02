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


public final class SimplifiedSelectTermFeature extends BinaryTermFeature {

    private final HeapLDT heapLDT;

    private SimplifiedSelectTermFeature(HeapLDT heapLDT) {
        this.heapLDT = heapLDT;
    }

    public static TermFeature create(HeapLDT heapLDT) {
        return new SimplifiedSelectTermFeature(heapLDT);
    }

    @Override
    protected boolean filter (Term t) {
            Boolean isSelectOp = heapLDT.getSortOfSelect(t.op()) != null;
            return  // either the operator is not a select operator
                    !isSelectOp ||
                    // or the heap term of the select operator is the base heap
                    // or another primitive heap variable
                    isPrimitiveHeapVariable(t.sub(0).op()) ||
                    // or the heap term of the select operator is an anon heap symbol
                    // (for instance an anonHeap function)
                    (   t.sub(0).op() instanceof Function &&
                        t.sub(0).op().arity() == 0 &&
                        t.sub(0).hasLabels() &&
                        t.sub(0).containsLabel(AnonHeapTermLabel.INSTANCE));

    }

    private boolean isPrimitiveHeapVariable(Operator op) {
        boolean isPrimitive = false;
        Iterator<LocationVariable> it = heapLDT.getAllHeaps().iterator();
        while(!isPrimitive && it.hasNext()) {
            isPrimitive = (it.next() == op);
        }
        return isPrimitive;
    }
}
