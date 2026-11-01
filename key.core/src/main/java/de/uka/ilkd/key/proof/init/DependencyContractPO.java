/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.init;

import java.util.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.speclang.DependencyContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.HeapContext;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * The proof obligation for dependency contracts.
 */
@NullMarked
public final class DependencyContractPO extends AbstractPO implements ContractPO {

    private @Nullable JTerm mbyAtPre;

    private final DependencyContract contract;

    private @Nullable InitConfig proofConfig;
    private @Nullable TermBuilder tb;


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

    /**
     * The {@link #tb} term builder and the heap LDT of the proof services are assigned by
     * {@link #postInit()} before this helper is invoked (see the field declaration); the
     * dereferences are suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    private JTerm buildFreePre(List<LocationVariable> heaps, @Nullable LocationVariable selfVar,
            KeYJavaType selfKJT, ImmutableList<LocationVariable> paramVars, JTerm wellFormedHeaps,
            Services services) throws ProofInputException {
        // "self != null"
        final JTerm selfNotNull =
            selfVar == null ? tb.tt() : tb.not(tb.equals(tb.var(selfVar), tb.NULL()));

        // "self.<created> = TRUE" for all heaps

        JTerm selfCreated = null;
        if (selfVar != null) {
            for (LocationVariable h : heaps) {
                final JTerm sc = tb.created(tb.var(h), tb.var(selfVar));
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
        // the sort of the receiver type is always set for a non-static target
        final JTerm selfExactType = selfVar == null ? tb.tt()
                : tb.exactInstance(Objects.requireNonNull(selfKJT.getSort()), tb.var(selfVar));


        // conjunction of...
        // - "p_i = null | p_i.<created> = TRUE" for object parameters, and
        // - "inBounds(p_i)" for integer parameters
        JTerm paramsOK = tb.tt();
        for (var paramVar : paramVars) {
            paramsOK = tb.and(paramsOK, tb.reachableValue(paramVar));
        }

        // initial value of measured_by clause
        final JTerm mbyAtPreDef;
        if (contract.hasMby()) {
            /*
             * final Function mbyAtPreFunc = new Function(new Name(TB.newName(services,
             * "mbyAtPre")), services.getTypeConverter() .getIntegerLDT() .targetSort());
             * register(mbyAtPreFunc); mbyAtPre = TB.func(mbyAtPreFunc);
             */
            final JTerm mby = contract.getMby(selfVar, paramVars, services);
            // mbyAtPreDef = TB.equals(mbyAtPre, mby);
            // the hasMby() guard above guarantees a measured-by term
            mbyAtPreDef = tb.measuredBy(Objects.requireNonNull(mby, "measured-by clause"));
        } else {
            // mbyAtPreDef = TB.tt();
            mbyAtPreDef = tb.measuredByEmpty();
        }

        return tb.and(wellFormedHeaps, selfNotNull, Objects.requireNonNull(selfCreated),
            selfExactType, paramsOK, mbyAtPreDef);
    }



    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    /**
     * The {@link #tb} term builder and the heap LDT of the proof services are set up by
     * {@link #postInit()} at the very beginning of this method (see the field declaration in
     * {@link AbstractPO}); the dereferences are suppressed with a scoped key. The mapping of a
     * modifiable heap to its {@code AtPre} variable deliberately stores {@code null} entries for
     * single-state targets (no {@code AtPre} variable exists then), and the contract translation
     * below ignores those entries; that intentionally nullable map value is suppressed with a
     * scoped key too.
     */
    @Override
    @SuppressWarnings({
        "nullness:dereference.of.nullable",
        "nullness:argument.type.incompatible" })
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
        if (target.getType() == KeYJavaType.VOID_TYPE) {
            throw new ProofInputException(
                "Dependency contracts are currently not supported for void methods");
        }

        final Services proofServices = postInit();

        // prepare variables
        final LocationVariable selfVar =
            !contract.getTarget().isStatic() ? tb.selfVar(contract.getKJT(), true) : null;
        final ImmutableList<LocationVariable> paramVars = tb.paramVars(target, true);

        final boolean twoState = (contract.getTarget().getStateCount() == 2);
        final int heapCount = contract.getTarget().getHeapCount(proofServices);

        final Map<LocationVariable, LocationVariable> preHeapVars =
            new LinkedHashMap<>();
        final Map<LocationVariable, LocationVariable> preHeapVarsReverse =
            new LinkedHashMap<>();
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

        JTerm permsFor = tb.tt();
        if (heapCount == 2
                && proofServices.getTypeConverter().getHeapLDT().getPermissionHeap() != null) {
            int stateCount = contract.getTarget().getStateCount();
            for (int i = 0; i < stateCount; i++) {
                LocationVariable h = heaps.get(i);
                LocationVariable p = heaps.get(i + stateCount);
                final JTerm pf = tb.permissionsFor(p, h);
                permsFor = tb.and(permsFor, pf);
            }
        }

        // register the variables and anon heap so they are declared in proof
        // header if the proof is saved to a file
        register(selfVar, proofServices);
        register(paramVars, proofServices);

        JTerm wellFormedHeaps = null;
        JTerm update = null;
        for (LocationVariable h : heaps) {
            final JTerm wellFormedHeap = tb.wellFormed(h);
            if (wellFormedHeaps == null) {
                wellFormedHeaps = wellFormedHeap;
            } else {
                wellFormedHeaps = tb.and(wellFormedHeaps, wellFormedHeap);
            }
            // prepare anon heap
            final Name anonHeapName = new Name(tb.newName("anon_" + h.toString()));
            final Function anonHeapFunc =
                new JFunction(anonHeapName, heapLDT.targetSort());
            register(anonHeapFunc, proofServices);
            final JTerm anonHeap =
                tb.label(tb.func(anonHeapFunc), ParameterlessTermLabel.ANON_HEAP_LABEL);
            final JTerm wellFormedAnonHeap = tb.wellFormed(anonHeap);
            if (wellFormedHeaps == null) {
                wellFormedHeaps = wellFormedAnonHeap;
            } else {
                wellFormedHeaps = tb.and(wellFormedHeaps, wellFormedAnonHeap);
            }
            // prepare update
            final boolean atPre = preHeapVars.containsValue(h);
            // a value found above is always a key of the reverse map, so the lookup cannot
            // miss; every modifiable heap of the target carries a dependency clause
            final LocationVariable depHeap =
                atPre ? Objects.requireNonNull(preHeapVarsReverse.get(h)) : h;
            final JTerm dep = Objects.requireNonNull(getContract().getDep(depHeap, atPre,
                selfVar, paramVars, preHeapVars, proofServices));
            final JTerm changedHeap = tb.anon(tb.var(h), tb.setMinus(tb.allLocs(), dep), anonHeap);
            final JTerm u = tb.elementary(h, changedHeap);
            if (update == null) {
                update = u;
            } else {
                update = tb.parallel(update, u);
            }
        }

        // translate contract
        final JTerm pre = tb.and(
            // a dependency contract always ranges over at least one modifiable heap
            buildFreePre(heaps, selfVar, contract.getKJT(), paramVars,
                Objects.requireNonNull(wellFormedHeaps, "no modifiable heaps"), proofServices),
            permsFor,
            Objects.requireNonNull(contract.getPre(heapLDT.getHeap(), selfVar, paramVars,
                preHeapVars, proofServices), "precondition of the dependency contract"));

        assert heaps.size() == heapCount * contract.getTarget().getStateCount();
        // prepare target term
        final JTerm[] subs =
            new JTerm[paramVars.size() + heaps.size() + (target.isStatic() ? 0 : 1)];
        int offset = 0;
        for (LocationVariable heap : heaps) {
            subs[offset++] = tb.var(heap);
        }
        if (!target.isStatic()) {
            // selfVar is only null for static targets, which the guard above excludes
            subs[offset++] = tb.var(Objects.requireNonNull(selfVar));
        }
        for (ProgramVariable paramVar : paramVars) {
            subs[offset++] = tb.var(paramVar);
        }
        final JTerm targetTerm = tb.func(target, subs);

        // build po
        // the update accumulator is non-null: each heap above contributes one elementary update
        final JTerm po =
            tb.imp(pre, tb.equals(targetTerm, tb.apply(Objects.requireNonNull(update),
                targetTerm, null)));

        // save in field
        assignPOTerms(po);

        // add axioms
        collectClassAxioms(contract.getKJT(), Objects.requireNonNull(proofConfig,
            "proofConfig is assigned by postInit()"));
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


    /**
     * The overridden declaration requires a non-null return type, but this implementation may
     * legitimately return {@code null}; the difference is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:override.return.invalid")
    @Override
    public @Nullable JTerm getMbyAtPre() {
        return mbyAtPre;
    }


    @Override
    public boolean equals(@Nullable Object o) {
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
    protected @Nullable InitConfig getCreatedInitConfigForSingleProof() {
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
