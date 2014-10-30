// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.collection.ImmutableList;
import java.util.LinkedHashSet;
import java.util.Map;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.util.InfFlowSpec;

/**
 * Walks through a java AST in depth-left-fist-order.
 * This walker is used collect all LocationVariables and optional function locations.
 */
public class ProgramVariableCollector extends JavaASTVisitor {

    private final LinkedHashSet<LocationVariable> result
        = new LinkedHashSet<LocationVariable>();

    /**
     * collects all program variables occuring in the AST <tt>root</tt>
     * using this constructor is equivalent to <tt>ProggramVariableCollector(root, false)</tt>
     * @param root the ProgramElement which is the root of the AST
     * @param services the Services object
     */
    public ProgramVariableCollector(ProgramElement root,
                                    Services services) {
    super(root, services);
        assert services != null;
        collectHeapVariables();
    }

    protected void collectHeapVariables() {
       HeapLDT ldt = services.getTypeConverter().getHeapLDT();
       for(LocationVariable heap: ldt.getAllHeaps()) {
          result.add(heap);
       }
    }


    @Override
    public void start() {
    walk(root());
    }


    public LinkedHashSet<LocationVariable> result() {
    return result;
    }

    @Override
    public String toString() {
    return result.toString();
    }

    @Override
    protected void doDefaultAction(SourceElement x) {
    }


    @Override
    public void performActionOnLocationVariable(LocationVariable x) {
        result.add(x);
    }


    @Override
    public void performActionOnLoopInvariant(LoopInvariant x) {
        TermProgramVariableCollector tpvc =
            services.getFactory().create(services);
        Term selfTerm = x.getInternalSelfTerm();

        Map<LocationVariable,Term> atPres = x.getInternalAtPres();

        //invariants
        for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
           Term inv = x.getInvariant(heap, selfTerm, atPres, services);
           if(inv != null) {
              inv.execPostOrder(tpvc);
           }
        }

        //modifies
        for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
           Term mod = x.getModifies(heap, selfTerm, atPres, services);
           if(mod != null) {
              mod.execPostOrder(tpvc);
           }
        }

       //information flow (TODO: does this really belong here?)
        for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            ImmutableList<InfFlowSpec> infFlowSpecs =
                   x.getInfFlowSpecs(heap, selfTerm, atPres, services);
            if (infFlowSpecs != null) {
                for (InfFlowSpec infFlowSpec : infFlowSpecs) {
                    for (Term t: infFlowSpec.preExpressions) {
                        t.execPostOrder(tpvc);
                    }
                    for (Term t: infFlowSpec.postExpressions) {
                        t.execPostOrder(tpvc);
                    }
                    for (Term t: infFlowSpec.newObjects) {
                        t.execPostOrder(tpvc);
                    }
                }
            }
        }

        //variant
        Term v = x.getVariant(selfTerm, atPres, services);
        if(v != null) {
            v.execPostOrder(tpvc);
        }

        result.addAll(tpvc.result());
    }


    @Override
    public void performActionOnBlockContract(BlockContract x) {
        TermProgramVariableCollector collector = services.getFactory().create(services);
        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            Term precondition = x.getPrecondition(heap, services);
            if (precondition != null) {
                precondition.execPostOrder(collector);
            }
        }
        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            Term postcondition = x.getPostcondition(heap, services);
            if (postcondition != null) {
                postcondition.execPostOrder(collector);
            }
        }
        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            Term modifiesClause = x.getModifiesClause(heap, services);
            if (modifiesClause != null) {
                modifiesClause.execPostOrder(collector);
            }
        }
        ImmutableList<InfFlowSpec> infFlowSpecs = x.getInfFlowSpecs();
        for (InfFlowSpec ts : infFlowSpecs) {
            for (Term t : ts.preExpressions) {
                t.execPostOrder(collector);
            }
            for (Term t : ts.postExpressions) {
                t.execPostOrder(collector);
            }
            for (Term t : ts.newObjects) {
                t.execPostOrder(collector);
            }
        }
        result.addAll(collector.result());
    }

}