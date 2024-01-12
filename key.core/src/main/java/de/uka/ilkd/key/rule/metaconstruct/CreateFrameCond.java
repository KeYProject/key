/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;

/**
 * Creates the frame condition (aka "assignable clause") for the given loop. Also accepts the
 * pre-state update and extracts the symbols from there. New symbols in the pre-state update (like
 * "heap_BeforeLOOP") are added to the namespaces. This is because the update is, for the loop scope
 * invariant taclet, created by a variable condition; new symbols created there are not
 * automatically stored in the proof, or will be generated/stored multiple times.
 *
 * @author Dominic Steinhoefel
 */
public final class CreateFrameCond extends AbstractTermTransformer {

    public CreateFrameCond() {
        super(new Name("#createFrameCond"), 4);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst, Services services) {
        final Term loopFormula = term.sub(0);
        final ProgramVariable heapBeforePV = //
            (ProgramVariable) term.sub(1).op();
        final ProgramVariable savedHeapBeforePV = //
            (ProgramVariable) term.sub(2).op();
        final ProgramVariable permissionsHeapBeforePV = //
            (ProgramVariable) term.sub(3).op();

        final Optional<LoopSpecification> loopSpec = //
            MiscTools.getSpecForTermWithLoopStmt(loopFormula, services);

        final boolean isTransaction = MiscTools.isTransaction((Modality) loopFormula.op());
        final boolean isPermissions = MiscTools.isPermissions(services);

        final Map<LocationVariable, Map<Term, Term>> heapToBeforeLoopMap = //
            createHeapToBeforeLoopMap(isTransaction, isPermissions, heapBeforePV, savedHeapBeforePV,
                permissionsHeapBeforePV, services);

        final Term frameCondition =
            createFrameCondition(loopSpec.get(), isTransaction, heapToBeforeLoopMap, services);

        return frameCondition;
    }

    /**
     * Creates the frame condition.
     *
     * @param loopSpec The {@link LoopSpecification}, for the modifies clause.
     * @param isTransaction A flag set to true iff the current modality is a transaction modality.
     * @param heapToBeforeLoopMap The map from heap variables to a map from original to pre-state
     *        terms.
     * @param services The {@link Services} object.
     * @return The frame condition.
     */
    private static Term createFrameCondition(final LoopSpecification loopSpec,
            final boolean isTransaction,
            final Map<LocationVariable, Map<Term, Term>> heapToBeforeLoopMap,
            final Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final Map<LocationVariable, Term> atPres = loopSpec.getInternalAtPres();
        final List<LocationVariable> heapContext = //
            HeapContext.getModHeaps(services, isTransaction);
        final Map<LocationVariable, Term> mods = new LinkedHashMap<>();
        heapContext.forEach(heap -> mods.put(heap,
            loopSpec.getModifies(heap, loopSpec.getInternalSelfTerm(), atPres, services)));

        Term frameCondition = null;
        for (LocationVariable heap : heapContext) {
            final Term mod = mods.get(heap);
            final Term fc;

            if (tb.strictlyNothing().equalsModIrrelevantTermLabels(mod)) {
                fc = tb.frameStrictlyEmpty(tb.var(heap), heapToBeforeLoopMap.get(heap));
            } else {
                fc = tb.frame(tb.var(heap), heapToBeforeLoopMap.get(heap), mod);
            }

            frameCondition = frameCondition == null ? fc : tb.and(frameCondition, fc);
        }

        return frameCondition;
    }

    /**
     * Creates the map from heap variables to a map from original terms to the pre-state terms.
     * Thereby, saves the new variables in the namespaces (which should not have occurred before!).
     *
     * @param isTransaction Signals that the current modality is a transaction modality.
     * @param isPermissions Signals that the current profile is one with permissions.
     * @param heapBeforePV The fresh PV for saving the standard heap.
     * @param savedHeapBeforePV The fresh PV for saving the transaction heap.
     * @param permissionsHeapBeforePV The fresh PV for saving the permissions heap.
     * @param services The {@link Services} object.
     *
     * @return A map from heap variables to a map from original terms to the pre-state terms.
     */
    private Map<LocationVariable, Map<Term, Term>> createHeapToBeforeLoopMap(boolean isTransaction,
            boolean isPermissions, ProgramVariable heapBeforePV, ProgramVariable savedHeapBeforePV,
            ProgramVariable permissionsHeapBeforePV, Services services) {
        final Map<LocationVariable, Map<Term, Term>> result = //
            new LinkedHashMap<>();
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final TermBuilder tb = services.getTermBuilder();

        put(result, heapLDT.getHeap(), tb.var(heapLDT.getHeap()), tb.var(heapBeforePV));

        if (isTransaction) {
            put(result, heapLDT.getSavedHeap(), tb.var(heapLDT.getSavedHeap()),
                tb.var(savedHeapBeforePV));
        }

        if (isPermissions) {
            put(result, heapLDT.getPermissionHeap(), tb.var(heapLDT.getPermissionHeap()),
                tb.var(permissionsHeapBeforePV));
        }

        return result;
    }

    private static void put(Map<LocationVariable, Map<Term, Term>> map, LocationVariable key,
            Term t1, Term t2) {
        map.computeIfAbsent(key, k -> new LinkedHashMap<>());
        map.get(key).put(t1, t2);
    }
}
