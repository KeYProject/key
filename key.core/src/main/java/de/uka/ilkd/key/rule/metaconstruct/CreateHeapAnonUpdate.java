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
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;

/**
 * Creates the anonymizing update for the heap. Expects as arguments the loop formula (for
 * determining the relevant heap contexts) and three Skolem terms for the currently implemented
 * heaps: The normal heap, the savedHeap for transactions, and the permissions heap.
 *
 * @author Dominic Steinhoefel
 */
public final class CreateHeapAnonUpdate extends AbstractTermTransformer {

    public CreateHeapAnonUpdate() {
        super(new Name("#createHeapAnonUpdate"), 4);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst, Services services) {
        final Term loopTerm = term.sub(0);
        final Optional<LoopSpecification> loopSpec = //
            MiscTools.getSpecForTermWithLoopStmt(loopTerm, services);

        if (!loopSpec.isPresent()) {
            return null;
        }

        final Term anonHeapTerm = term.sub(1);
        final Term anonSavedHeapTerm = term.sub(2);
        final Term anonPermissionsHeapTerm = term.sub(3);

        return createHeapAnonUpdate(loopSpec.get(),
            MiscTools.isTransaction((Modality) loopTerm.op()), MiscTools.isPermissions(services),
            anonHeapTerm, anonSavedHeapTerm, anonPermissionsHeapTerm, services);
    }

    /**
     * Creates the anonymizing update for the given loop specification.
     *
     * @param loopSpec The {@link LoopSpecification}.
     * @param isTransaction set to true iff we're in a transaction modality (then, there are more
     *        heaps available).
     * @param isPermissions set to true if the permissions profile is active (then, the permissions
     *        heap is available).
     * @param anonHeapTerm The term with the Skolem heap.
     * @param anonSavedHeapTerm The term with the Skolem saved heap.
     * @param anonPermissionsHeapTerm The term with the Skolem permissions heap.
     * @param services The {@link Services} object (for the {@link TermBuilder}).
     * @return The anonymizing update.
     */
    private static Term createHeapAnonUpdate(LoopSpecification loopSpec, boolean isTransaction,
            boolean isPermissions, Term anonHeapTerm, Term anonSavedHeapTerm,
            Term anonPermissionsHeapTerm, Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final Map<LocationVariable, Term> atPres = loopSpec.getInternalAtPres();
        final List<LocationVariable> heapContext = //
            HeapContext.getModHeaps(services, isTransaction);
        final Map<LocationVariable, Term> mods = new LinkedHashMap<>();
        // The call to MiscTools.removeSingletonPVs removes from the assignable clause
        // the program variables which of course should not be part of an anonymizing
        // heap expression. The reason why they're there at all is that for Abstract
        // Execution, it actually makes sense to have program variables in assignable
        // clauses, since for an abstract statement they cannot be extracted like for
        // concrete statements (such as loop bodies). (DS, 2019-07-05)
        heapContext.forEach(heap -> mods.put(heap,
            loopSpec.getModifies(heap, loopSpec.getInternalSelfTerm(), atPres, services)));

        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();

        Term anonUpdate = tb.skip();

        anonUpdate = tb.parallel(anonUpdate, createElementaryAnonUpdate(heapLDT.getHeap(),
            anonHeapTerm, mods.get(heapLDT.getHeap()), services));

        if (isTransaction) {
            anonUpdate = tb.parallel(anonUpdate, createElementaryAnonUpdate(heapLDT.getSavedHeap(),
                anonHeapTerm, mods.get(heapLDT.getSavedHeap()), services));
        }

        if (isPermissions) {
            anonUpdate =
                tb.parallel(anonUpdate, createElementaryAnonUpdate(heapLDT.getPermissionHeap(),
                    anonPermissionsHeapTerm, mods.get(heapLDT.getPermissionHeap()), services));
        }

        return anonUpdate;
    }

    /**
     * Creates an elementary "heap := anon_heap_LOOP<<anonHeapFunction>>" update, or a Skip update
     * if the mod signals that nothing is modified.
     *
     * @param heap The heap variable.
     * @param anonHeap The anonymized heap term.
     * @param mod The modifies clause, only for checking whether it's strictly nothing (then the
     *        elementary update is a skip).
     * @param services The {@link Services} object (for the {@link TermBuilder}).
     * @return An elementary anonymizing heap update.
     */
    private static Term createElementaryAnonUpdate(LocationVariable heap, Term anonHeap, Term mod,
            Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final Term anonHeapTerm = tb.label(anonHeap, ParameterlessTermLabel.ANON_HEAP_LABEL);

        return tb.strictlyNothing().equalsModIrrelevantTermLabels(mod) ? tb.skip()
                : tb.anonUpd(heap, mod, anonHeapTerm);
    }

}
