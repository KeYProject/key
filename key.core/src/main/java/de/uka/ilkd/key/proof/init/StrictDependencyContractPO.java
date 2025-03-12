/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.speclang.DependencyContract;
import de.uka.ilkd.key.speclang.HeapContext;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;


/**
 * A strict proof obligation for dependency contracts on methods.
 * The relaxed proof obligation (DependencyContractPO) only verifies that
 * the return value of a method only depends on the locations in the accessible
 * clause. In contrast, this proof obligation additionally verifies that any
 * objects on the heap (except those newly created) only depend on the locations
 * in the accessible clause.
 * For non-methods, this proof obligation is identical to DependencyContractPO.
 */
public class StrictDependencyContractPO extends DependencyContractPO {
    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public StrictDependencyContractPO(InitConfig initConfig, DependencyContract contract) {
        super(initConfig, contract);
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    @Override
    public void readProblem() throws ProofInputException {
        assert proofConfig == null;
        IObserverFunction target = contract.getTarget();

        // This StrictDependencyPO can only handle accessible clauses on methods.
        // Therefore, dispatch to the relaxed DependencyPO when not applicable.
        if (!(target instanceof IProgramMethod)) {
            super.readProblem();
            return;
        }
        target = javaInfo.getToplevelPM(contract.getKJT(), (IProgramMethod) target);

        // NOTE: This FIXME is duplicated from DependencyPO::readProblem.
        // FIXME: for some reason the above method call returns null now and then, the
        // following
        // line (hopefully) is a work-around
        if (target == null) {
            target = contract.getTarget();
        }

        final boolean isVoid = target.getType() == KeYJavaType.VOID_TYPE;

        final Services proofServices = postInit();

        // prepare variables
        final LocationVariable selfVar =
            !contract.getTarget().isStatic() ? tb.selfVar(contract.getKJT(), true) : null;
        final ImmutableList<LocationVariable> paramVars = tb.paramVars(target, true);

        final boolean twoState = (contract.getTarget().getStateCount() == 2);
        final int heapCount = contract.getTarget().getHeapCount(proofServices);

        final Map<LocationVariable, LocationVariable> preHeapVars = new LinkedHashMap<>();
        final Map<LocationVariable, LocationVariable> preHeapVarsReverse = new LinkedHashMap<>();
        List<LocationVariable> heaps = new LinkedList<>();
        int hc = 0;
        for (LocationVariable h : HeapContext.getModifiableHeaps(proofServices, false)) {
            if (hc >= heapCount) {
                break;
            }
            heaps.add(h);
            LocationVariable preVar =
                twoState ? tb.atPreVar(h.name().toString(), h.sort(), true) : null;
            if (preVar != null) {
                register(preVar, proofServices);
                heaps.add(preVar);
            }
            preHeapVars.put(h, preVar);
            if (preVar != null) {
                preHeapVarsReverse.put(preVar, h);
            }
        }

        Term permsFor = tb.tt();
        if (heapCount == 2
                && proofServices.getTypeConverter().getHeapLDT().getPermissionHeap() != null) {
            int stateCount = contract.getTarget().getStateCount();
            for (int i = 0; i < stateCount; i++) {
                LocationVariable h = heaps.get(i);
                LocationVariable p = heaps.get(i + stateCount);
                final Term pf = tb.permissionsFor(p, h);
                permsFor = tb.and(permsFor, pf);
            }
        }

        // register the variables and anon heap so they are declared in proof
        // header if the proof is saved to a file
        register(selfVar, proofServices);
        register(paramVars, proofServices);

        Term wellFormedHeaps = null;
        Term update = null;
        for (LocationVariable h : heaps) {
            final Term wellFormedHeap = tb.wellFormed(h);
            if (wellFormedHeaps == null) {
                wellFormedHeaps = wellFormedHeap;
            } else {
                wellFormedHeaps = tb.and(wellFormedHeaps, wellFormedHeap);
            }
            // prepare anon heap
            final Name anonHeapName = new Name(tb.newName("anon_" + h.toString()));
            final JFunction anonHeapFunc = new JFunction(anonHeapName, heapLDT.targetSort());
            register(anonHeapFunc, proofServices);
            final Term anonHeap =
                tb.label(tb.func(anonHeapFunc), ParameterlessTermLabel.ANON_HEAP_LABEL);
            final Term wellFormedAnonHeap = tb.wellFormed(anonHeap);
            if (wellFormedHeaps == null) {
                wellFormedHeaps = wellFormedAnonHeap;
            } else {
                wellFormedHeaps = tb.and(wellFormedHeaps, wellFormedAnonHeap);
            }
            // prepare update
            final boolean atPre = preHeapVars.containsValue(h);
            final Term dep = getContract().getDep(atPre ? preHeapVarsReverse.get(h) : h, atPre,
                selfVar, paramVars, preHeapVars, proofServices);
            final Term changedHeap = tb.anon(tb.var(h), tb.setMinus(tb.allLocs(), dep), anonHeap);
            final Term u = tb.elementary(h, changedHeap);
            if (update == null) {
                update = u;
            } else {
                update = tb.parallel(update, u);
            }
        }

        // translate contract
        final Term pre = tb.and(
            buildFreePre(heaps, selfVar, contract.getKJT(), paramVars, wellFormedHeaps,
                proofServices),
            permsFor,
            contract.getPre(heapLDT.getHeap(), selfVar, paramVars, preHeapVars, proofServices));

        assert heaps.size() == heapCount * contract.getTarget().getStateCount();

        LocationVariable heapVar = (LocationVariable) tb.getBaseHeap().op();
        final Term dep =
            contract.getDep(heapVar, false, selfVar, paramVars, preHeapVars, proofServices);
        final Term assignable = contract.getModifiable(heapVar, selfVar, paramVars, proofServices);

        final HeapLDT heapldt = proofServices.getTypeConverter().getHeapLDT();
        final Sort heapSort = heapldt.targetSort();
        final var heapVar1 = new JFunction(new Name(tb.newName(heapSort)), heapSort);
        register(heapVar1, proofServices);
        final var heapVar2 = new JFunction(new Name(tb.newName(heapSort)), heapSort);
        register(heapVar2, proofServices);
        final var heapTerm1 = tb.func(heapVar1);
        final var heapTerm2 = tb.func(heapVar2);

        // Effects on heap is the same
        final Sort objectSort = proofServices.getJavaInfo().objectSort();
        final Sort fieldSort = proofServices.getTypeConverter().getHeapLDT().getFieldSort();
        final var objectVar = new LogicVariable(new Name(tb.newName(objectSort)), objectSort);
        final var fieldVar = new LogicVariable(new Name(tb.newName(fieldSort)), fieldSort);
        Term objectTerm = tb.var(objectVar);
        Term fieldTerm = tb.var(fieldVar);
        final Term heapCheck = tb.all(objectVar,
            tb.all(fieldVar,
                tb.imp(tb.and(tb.subset(tb.singleton(objectTerm, fieldTerm), assignable),
                    tb.not(tb.elementOf(objectTerm, fieldTerm, tb.freshLocs(tb.getBaseHeap()))),
                    tb.not(tb.equals(fieldTerm, tb.func(heapldt.getCreated())))),
                    tb.equals(tb.select(JavaDLTheory.ANY, heapTerm1, objectTerm, fieldTerm),
                        tb.select(JavaDLTheory.ANY, heapTerm2, objectTerm, fieldTerm)))));

        // Result is the same
        final Sort resultSort = target.sort();
        final LocationVariable resultVar1 = isVoid ? null
                : new LocationVariable(new ProgramElementName(tb.newName(resultSort)),
                    new KeYJavaType(resultSort));
        register(resultVar1, proofServices);
        final JFunction resultConst1 = new JFunction(new Name(tb.newName(resultSort)), resultSort);
        register(resultConst1, proofServices);
        final LocationVariable resultVar2 = isVoid ? null
                : new LocationVariable(new ProgramElementName(tb.newName(resultSort)),
                    new KeYJavaType(resultSort));
        register(resultVar2, proofServices);
        final JFunction resultConst2 = new JFunction(new Name(tb.newName(resultSort)), resultSort);
        register(resultConst2, proofServices);
        final Term resultCheck =
            isVoid ? tb.tt() : tb.equals(tb.func(resultConst1), tb.func(resultConst2));

        // Method call modalities
        final Term normalCall =
            buildModality(target, selfVar, paramVars, resultVar1, resultConst1, heapVar1);
        final Term anonCall = tb.apply(update,
            buildModality(target, selfVar, paramVars, resultVar2, resultConst2, heapVar2));

        // build po
        final Term po = tb.imp(tb.and(pre, normalCall, anonCall),
            tb.and(tb.subset(assignable, dep), resultCheck, heapCheck));

        // save in field
        assignPOTerms(po);

        // add axioms
        collectClassAxioms(contract.getKJT(), proofConfig);
    }

    private Term buildModality(IObserverFunction target, LocationVariable selfVar,
            ImmutableList<LocationVariable> params, LocationVariable resultVar,
            JFunction resultConst,
            JFunction heap) {
        var jb = buildMethodCall(target, selfVar, params, resultVar);
        return tb.dia(jb,
            tb.and(tb.equals(tb.func(heap), tb.getBaseHeap()),
                tb.equals(tb.func(resultConst), tb.var(resultVar))));
    }

    private JavaBlock buildMethodCall(IObserverFunction target, LocationVariable selfVar,
            ImmutableList<LocationVariable> params, LocationVariable result) {
        if (!(target instanceof IProgramMethod m)) {
            throw new IllegalArgumentException("Expected target to be a method");
        }
        Statement callStmt = new MethodBodyStatement(m, selfVar, result,
            new ImmutableArray<>(params.toArray(LocationVariable.class)));
        return JavaBlock.createJavaBlock(new StatementBlock(callStmt));
    }

    private Services postInit() {
        proofConfig = environmentConfig.deepCopy();
        final Services proofServices = proofConfig.getServices();
        tb = proofServices.getTermBuilder();
        return proofServices;
    }

    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof StrictDependencyContractPO cPO)) {
            return false;
        }
        return contract.equals(cPO.contract);
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof StrictDependencyContractPO sdpo)) {
            return false;
        } else {
            return contract.equals(sdpo.contract);
        }
    }
}
