/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import java.util.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.speclang.DependencyContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.HeapContext;

import org.key_project.util.collection.ImmutableList;


/**
 * The proof obligation for dependency contracts.
 */
public final class DependencyContractPO extends AbstractPO implements ContractPO {

    private Term mbyAtPre;

    private final DependencyContract contract;

    private InitConfig proofConfig;
    private TermBuilder tb;


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public DependencyContractPO(InitConfig initConfig, DependencyContract contract) {
        super(initConfig, contract.getName());
        assert !(contract instanceof FunctionalOperationContract);
        this.contract = contract;
    }



    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    private Term buildFreePre(List<LocationVariable> heaps, ProgramVariable selfVar,
            KeYJavaType selfKJT, ImmutableList<ProgramVariable> paramVars, Term wellFormedHeaps,
            Services services) throws ProofInputException {
        // "self != null"
        final Term selfNotNull =
            selfVar == null ? tb.tt() : tb.not(tb.equals(tb.var(selfVar), tb.NULL()));

        // "self.<created> = TRUE" for all heaps

        Term selfCreated = null;
        if (selfVar != null) {
            for (LocationVariable h : heaps) {
                final Term sc = tb.created(tb.var(h), tb.var(selfVar));
                if (selfCreated == null) {
                    selfCreated = sc;
                } else {
                    selfCreated = tb.and(selfCreated, sc);
                }
            }
        } else {
            selfCreated = tb.tt();
        }

        // "MyClass::exactInstance(self) = TRUE"
        final Term selfExactType =
            selfVar == null ? tb.tt() : tb.exactInstance(selfKJT.getSort(), tb.var(selfVar));


        // conjunction of...
        // - "p_i = null | p_i.<created> = TRUE" for object parameters, and
        // - "inBounds(p_i)" for integer parameters
        Term paramsOK = tb.tt();
        for (ProgramVariable paramVar : paramVars) {
            paramsOK = tb.and(paramsOK, tb.reachableValue(paramVar));
        }

        // initial value of measured_by clause
        final Term mbyAtPreDef;
        if (contract.hasMby()) {
            /*
             * final Function mbyAtPreFunc = new Function(new Name(TB.newName(services,
             * "mbyAtPre")), services.getTypeConverter() .getIntegerLDT() .targetSort());
             * register(mbyAtPreFunc); mbyAtPre = TB.func(mbyAtPreFunc);
             */
            final Term mby = contract.getMby(selfVar, paramVars, services);
            // mbyAtPreDef = TB.equals(mbyAtPre, mby);
            mbyAtPreDef = tb.measuredBy(mby);
        } else {
            // mbyAtPreDef = TB.tt();
            mbyAtPreDef = tb.measuredByEmpty();
        }

        return tb.and(wellFormedHeaps, selfNotNull, selfCreated, selfExactType, paramsOK,
            mbyAtPreDef);
    }



    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    @Override
    public void readProblem() throws ProofInputException {
        assert proofConfig == null;
        IObserverFunction target = contract.getTarget();
        if (target instanceof IProgramMethod) {
            target = javaInfo.getToplevelPM(contract.getKJT(), (IProgramMethod) target);
            // FIXME: for some reason the above method call returns null now and then, the following
            // line (hopefully) is a work-around
            if (target == null) {
                target = contract.getTarget();
            }
        }

        final Services proofServices = postInit();

        // prepare variables
        final ProgramVariable selfVar =
            !contract.getTarget().isStatic() ? tb.selfVar(contract.getKJT(), true) : null;
        final ImmutableList<ProgramVariable> paramVars = tb.paramVars(target, true);

        final boolean twoState = (contract.getTarget().getStateCount() == 2);
        final int heapCount = contract.getTarget().getHeapCount(proofServices);

        final Map<LocationVariable, LocationVariable> preHeapVars =
            new LinkedHashMap<>();
        final Map<LocationVariable, LocationVariable> preHeapVarsReverse =
            new LinkedHashMap<>();
        List<LocationVariable> heaps = new LinkedList<>();
        int hc = 0;
        for (LocationVariable h : HeapContext.getModHeaps(proofServices, false)) {
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
            final Function anonHeapFunc = new Function(anonHeapName, heapLDT.targetSort());
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
        // prepare target term
        final Term[] subs = new Term[paramVars.size() + heaps.size() + (target.isStatic() ? 0 : 1)];
        int offset = 0;
        for (LocationVariable heap : heaps) {
            subs[offset++] = tb.var(heap);
        }
        if (!target.isStatic()) {
            subs[offset++] = tb.var(selfVar);
        }
        for (ProgramVariable paramVar : paramVars) {
            subs[offset++] = tb.var(paramVar);
        }
        final Term targetTerm = tb.func(target, subs);

        // build po
        final Term po = tb.imp(pre, tb.equals(targetTerm, tb.apply(update, targetTerm, null)));

        // save in field
        assignPOTerms(po);

        // add axioms
        collectClassAxioms(contract.getKJT(), proofConfig);
    }



    private Services postInit() {
        proofConfig = environmentConfig.deepCopy();
        final Services proofServices = proofConfig.getServices();
        tb = proofServices.getTermBuilder();
        return proofServices;
    }


    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof DependencyContractPO cPO)) {
            return false;
        }
        return contract.equals(cPO.contract);
    }


    @Override
    public DependencyContract getContract() {
        return contract;
    }


    @Override
    public Term getMbyAtPre() {
        return mbyAtPre;
    }


    @Override
    public boolean equals(Object o) {
        if (!(o instanceof DependencyContractPO)) {
            return false;
        } else {
            return contract.equals(((DependencyContractPO) o).contract);
        }
    }


    @Override
    public int hashCode() {
        return contract.hashCode();
    }

    /**
     * {@inheritDoc}
     *
     * @return
     */
    @Override
    public Configuration createLoaderConfig() {
        var c = super.createLoaderConfig();
        c.set("contract", contract.getName());
        return c;
    }


    @Override
    protected InitConfig getCreatedInitConfigForSingleProof() {
        return proofConfig;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public KeYJavaType getContainerType() {
        return getContract().getKJT();
    }
}
