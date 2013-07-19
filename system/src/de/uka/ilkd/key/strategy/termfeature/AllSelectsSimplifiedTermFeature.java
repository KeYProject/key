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
import de.uka.ilkd.key.logic.AuxiliaryTermLabel;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;


public final class AllSelectsSimplifiedTermFeature extends BinaryTermFeature {

    private final HeapLDT heapLDT;

    private AllSelectsSimplifiedTermFeature(HeapLDT heapLDT) {
        this.heapLDT = heapLDT;
    }

    public static TermFeature create(HeapLDT heapLDT) {
        return new AllSelectsSimplifiedTermFeature(heapLDT);
    }

    @Override
    protected boolean filter (Term t) {
        SelectsSimplifiedVisitor visitor =
                new SelectsSimplifiedVisitor(heapLDT);
        t.execPreOrder(visitor);
        return visitor.getResult();
    }


    private class SelectsSimplifiedVisitor implements Visitor {
        private boolean selectsSimplified;
        private final HeapLDT heapLDT;

        public SelectsSimplifiedVisitor(HeapLDT heapLDT) {
            this.heapLDT = heapLDT;
            this.selectsSimplified = true;
        }

        @Override
        public void visit(Term visited) {
            Operator op = visited.op();
            Boolean isSelectOp = heapLDT.getSortOfSelect(op) != null;
            selectsSimplified = selectsSimplified &&
                                (   // either the operator is not a select operator
                                    !isSelectOp ||
                                    // or the heap term of the select operator is the base heap
                                    visited.sub(0).op() == heapLDT.getHeap() ||
                                    // or the heap term of the select operator is an auxiliary heap symbol
                                    // (for instance an anonHeap function)
                                    (   visited.sub(0).hasLabels() &&
                                        visited.sub(0).containsLabel(AuxiliaryTermLabel.INSTANCE) &&
                                        visited.sub(0).op().arity() == 0 &&
                                        visited.sub(0).op() instanceof Function));
        }


        @Override
        public void subtreeEntered(Term subtreeRoot) {
            // nothing to do
        }


        @Override
        public void subtreeLeft(Term subtreeRoot) {
            // nothing to do
        }

        public boolean getResult() {
            return selectsSimplified;
        }
    }

}
