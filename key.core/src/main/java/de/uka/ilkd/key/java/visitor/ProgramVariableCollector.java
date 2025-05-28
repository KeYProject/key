/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.visitor;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Objects;

import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractionPredicate;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.statement.JmlAssert;
import de.uka.ilkd.key.java.statement.SetStatement;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.LoopContract;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.speclang.MergeContract;
import de.uka.ilkd.key.speclang.PredicateAbstractionMergeContract;
import de.uka.ilkd.key.speclang.UnparameterizedMergeContract;
import de.uka.ilkd.key.util.InfFlowSpec;

import org.key_project.util.collection.ImmutableList;

/**
 * Walks through a java AST in depth-left-fist-order. This walker is used collect all
 * LocationVariables and optional function locations.
 */
public class ProgramVariableCollector extends JavaASTVisitor {

    private final LinkedHashSet<LocationVariable> result = new LinkedHashSet<>();

    /**
     * collects all program variables occurring in the AST <tt>root</tt> using this constructor is
     * equivalent to <tt>ProggramVariableCollector(root, false)</tt>
     *
     * @param root the ProgramElement which is the root of the AST
     * @param services the Services object
     */
    public ProgramVariableCollector(ProgramElement root, Services services) {
        super(root, services);
        assert services != null;
        collectHeapVariables();
    }

    protected void collectHeapVariables() {
        HeapLDT ldt = services.getTypeConverter().getHeapLDT();
        for (LocationVariable heap : ldt.getAllHeaps()) {
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
    public void performActionOnMergeContract(MergeContract x) {
        assert (x instanceof UnparameterizedMergeContract)
                || (x instanceof PredicateAbstractionMergeContract)
                : "Unexpected type of merge contract: " + x.getClass().getSimpleName();

        if (x instanceof UnparameterizedMergeContract) {
            return;
        }

        PredicateAbstractionMergeContract pamc = (PredicateAbstractionMergeContract) x;

        TermProgramVariableCollector tpvc = services.getFactory().create(services);

        Map<LocationVariable, JTerm> atPres = pamc.getAtPres();

        final ArrayList<AbstractionPredicate> preds =
            pamc.getAbstractionPredicates(atPres, services);
        preds.forEach(pred -> pred.getPredicateFormWithPlaceholder().second.execPostOrder(tpvc));

        result.addAll(tpvc.result());
    }

    @Override
    public void performActionOnLoopInvariant(LoopSpecification x) {
        TermProgramVariableCollector tpvc = services.getFactory().create(services);
        JTerm selfTerm = x.getInternalSelfTerm();

        Map<LocationVariable, JTerm> atPres = x.getInternalAtPres();

        // invariants
        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            JTerm inv = x.getInvariant(heap, selfTerm, atPres, services);
            if (inv != null) {
                inv.execPostOrder(tpvc);
            }
        }

        // free invariants
        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            JTerm inv = x.getFreeInvariant(heap, selfTerm, atPres, services);
            if (inv != null) {
                inv.execPostOrder(tpvc);
            }
        }

        // modifiable
        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            JTerm modifiable = x.getModifiable(heap, selfTerm, atPres, services);
            if (modifiable != null) {
                modifiable.execPostOrder(tpvc);
            }
        }

        // free modifiable
        for (LocationVariable heap : services.getTypeConverter().getHeapLDT()
                .getAllHeaps()) {
            JTerm freeModifiable = x.getFreeModifiable(heap, selfTerm, atPres, services);
            if (freeModifiable != null) {
                freeModifiable.execPostOrder(tpvc);
            }
        }

        // information flow (TODO: does this really belong here?)
        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            ImmutableList<InfFlowSpec> infFlowSpecs =
                x.getInfFlowSpecs(heap, selfTerm, atPres, services);
            if (infFlowSpecs != null) {
                for (InfFlowSpec infFlowSpec : infFlowSpecs) {
                    for (JTerm t : infFlowSpec.preExpressions) {
                        t.execPostOrder(tpvc);
                    }
                    for (JTerm t : infFlowSpec.postExpressions) {
                        t.execPostOrder(tpvc);
                    }
                    for (JTerm t : infFlowSpec.newObjects) {
                        t.execPostOrder(tpvc);
                    }
                }
            }
        }

        // variant
        JTerm v = x.getVariant(selfTerm, atPres, services);
        if (v != null) {
            v.execPostOrder(tpvc);
        }

        result.addAll(tpvc.result());
    }

    @Override
    public void performActionOnBlockContract(BlockContract x) {
        TermProgramVariableCollector collector = services.getFactory().create(services);
        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            JTerm precondition = x.getPrecondition(heap, services);
            if (precondition != null) {
                precondition.execPostOrder(collector);
            }

            JTerm freePrecondition = x.getFreePrecondition(heap, services);
            if (freePrecondition != null) {
                freePrecondition.execPostOrder(collector);
            }
        }
        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            JTerm postcondition = x.getPostcondition(heap, services);
            if (postcondition != null) {
                postcondition.execPostOrder(collector);
            }

            JTerm freePostcondition = x.getFreePostcondition(heap, services);
            if (freePostcondition != null) {
                freePostcondition.execPostOrder(collector);
            }
        }
        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            JTerm modifiableClause = x.getModifiableClause(heap, services);
            if (modifiableClause != null) {
                modifiableClause.execPostOrder(collector);
            }
        }
        ImmutableList<InfFlowSpec> infFlowSpecs = x.getInfFlowSpecs();
        for (InfFlowSpec ts : infFlowSpecs) {
            for (JTerm t : ts.preExpressions) {
                t.execPostOrder(collector);
            }
            for (JTerm t : ts.postExpressions) {
                t.execPostOrder(collector);
            }
            for (JTerm t : ts.newObjects) {
                t.execPostOrder(collector);
            }
        }
        result.addAll(collector.result());
    }

    @Override
    public void performActionOnLoopContract(LoopContract x) {
        TermProgramVariableCollector collector = services.getFactory().create(services);
        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            JTerm precondition = x.getPrecondition(heap, services);
            if (precondition != null) {
                precondition.execPostOrder(collector);
            }

            JTerm freePrecondition = x.getFreePrecondition(heap, services);
            if (freePrecondition != null) {
                freePrecondition.execPostOrder(collector);
            }
        }
        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            JTerm postcondition = x.getPostcondition(heap, services);
            if (postcondition != null) {
                postcondition.execPostOrder(collector);
            }

            JTerm freePostcondition = x.getFreePostcondition(heap, services);
            if (freePostcondition != null) {
                freePostcondition.execPostOrder(collector);
            }
        }
        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            JTerm modifiableClause = x.getModifiableClause(heap, services);
            if (modifiableClause != null) {
                modifiableClause.execPostOrder(collector);
            }
        }
        ImmutableList<InfFlowSpec> infFlowSpecs = x.getInfFlowSpecs();
        for (InfFlowSpec ts : infFlowSpecs) {
            for (JTerm t : ts.preExpressions) {
                t.execPostOrder(collector);
            }
            for (JTerm t : ts.postExpressions) {
                t.execPostOrder(collector);
            }
            for (JTerm t : ts.newObjects) {
                t.execPostOrder(collector);
            }
        }
        result.addAll(collector.result());
    }


    @Override
    public void performActionOnJmlAssert(final JmlAssert x) {
        handleJmlStatement(x);
    }

    @Override
    public void performActionOnSetStatement(SetStatement x) {
        handleJmlStatement(x);
    }

    private void handleJmlStatement(Statement x) {
        TermProgramVariableCollector tpvc = services.getFactory().create(services);
        var spec =
            Objects.requireNonNull(services.getSpecificationRepository().getStatementSpec(x));
        for (JTerm v : spec.vars().atPres.values()) {
            v.execPostOrder(tpvc);
        }
        for (JTerm v : spec.vars().atBefores.values()) {
            v.execPostOrder(tpvc);
        }

        for (JTerm term : spec.terms()) {
            term.execPostOrder(tpvc);
        }
        result.addAll(tpvc.result());
    }


}
