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

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Operator;


public final class ContainsIfThenElseTermFeature extends BinaryTermFeature {

    public static final ContainsIfThenElseTermFeature INSTANCE =
            new ContainsIfThenElseTermFeature();


    private ContainsIfThenElseTermFeature() {
    }


    @Override
    protected boolean filter(Term t) {
        ContainsIfThenElseVisitor visitor =
                new ContainsIfThenElseVisitor();
        t.execPreOrder(visitor);
        return visitor.getResult();
    }


    private class ContainsIfThenElseVisitor implements Visitor {

        private boolean containsIfThenElse;


        public ContainsIfThenElseVisitor() {
            this.containsIfThenElse = false;
        }


        @Override
        public void visit(Term visited) {
            Operator op = visited.op();
            containsIfThenElse = containsIfThenElse ||
                                 op == IfThenElse.IF_THEN_ELSE;
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
            return containsIfThenElse;
        }
    }

}
