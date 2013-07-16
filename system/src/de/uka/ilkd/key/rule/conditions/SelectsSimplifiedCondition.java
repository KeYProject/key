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
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.AuxiliaryTermLabel;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import java.util.logging.Level;
import java.util.logging.Logger;


public final class SelectsSimplifiedCondition extends VariableConditionAdapter {

    private final SchemaVariable reference;

    private final boolean negation;


    public SelectsSimplifiedCondition(SchemaVariable reference,
                                      boolean negation) {
        this.reference = reference;
        this.negation = negation;
    }


    @Override
    public boolean check(SchemaVariable var,
                         SVSubstitute subst,
                         SVInstantiations svInst,
                         Services services) {
        if (var == reference) {
            if (subst instanceof Term) {
                Term substTerm = (Term) subst;
                SelectsSimplifiedVisitor visitor =
                        new SelectsSimplifiedVisitor(services);
                substTerm.execPreOrder(visitor);
                return negation ^ visitor.getResult();
            } else {
                Logger.getGlobal().log(Level.WARNING,
                                       "Warning: SelectsSimplifiedCondition " +
                                       "expects a term as substitute.");
                return false;
            }
        }
        return true;
    }


    @Override
    public String toString() {
        return (negation ? " \\not " : "") + "\\selectsSimplified(" + reference +
               ")";
    }


    private class SelectsSimplifiedVisitor implements Visitor {
        private boolean selectsSimplified;
        private final Services services;

        public SelectsSimplifiedVisitor(Services services) {
            this.services = services;
            this.selectsSimplified = true;
        }

        @Override
        public void visit(Term visited) {
            Operator op = visited.op();
            HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
            Boolean isSelectOp = heapLDT.getSortOfSelect(op) != null;
            selectsSimplified = selectsSimplified &&
                                (   // either the operator is no select operator
                                    !isSelectOp ||
                                    // or the heap term of the select operator is the base heap
                                    visited.sub(0).op() == heapLDT.getHeap() ||
                                    // or the heap term of the select operator is an auxiliary heap symbol
                                    // (for instance an anonHeap function)
                                    (   visited.sub(0).op().arity() == 0 &&
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
