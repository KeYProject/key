/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.UpdateableOperator;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;

/**
 * Initializes the "before loop" update needed for the assignable clause.
 *
 * Only remembers the heaps of the context, not the changed local variables, although this is done
 * for the built-in loop invariant rules, where they however are never used.
 *
 * NOTE: If the local variables should be remembered, we have to find a way to declare them globally
 * in taclets, which currently is not possible for statically unknown lists of variables. Variable
 * conditions cannot access the goal-local namespaces, only the global one.
 *
 * Expects as arguments the loop formula (for determining the relevant heap contexts) and three
 * Skolem terms for the currently implemented heaps: The normal heap, the savedHeap for
 * transactions, and the permissions heap.
 *
 * @author Dominic Steinhoefel
 */
public final class CreateBeforeLoopUpdate extends AbstractTermTransformer {

    public CreateBeforeLoopUpdate() {
        super(new Name("#createBeforeLoopUpdate"), 4);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst, Services services) {
        final Term loopTerm = term.sub(0);

        final Term anonHeapTerm = term.sub(1);
        final Term anonSavedHeapTerm = term.sub(2);
        final Term anonPermissionsHeapTerm = term.sub(3);

        return createBeforeLoopUpdate(MiscTools.isTransaction((Modality) loopTerm.op()),
            MiscTools.isPermissions(services), anonHeapTerm, anonSavedHeapTerm,
            anonPermissionsHeapTerm, services);
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
    private static Term createBeforeLoopUpdate(boolean isTransaction, boolean isPermissions,
            Term anonHeapTerm, Term anonSavedHeapTerm, Term anonPermissionsHeapTerm,
            Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();

        Term beforeLoopUpdate =
            tb.elementary((UpdateableOperator) anonHeapTerm.op(), tb.var(heapLDT.getHeap()));

        if (isTransaction) {
            beforeLoopUpdate = tb.parallel(beforeLoopUpdate, tb.elementary(
                (UpdateableOperator) anonSavedHeapTerm.op(), tb.var(heapLDT.getSavedHeap())));
        }

        if (isPermissions) {
            beforeLoopUpdate = tb.parallel(beforeLoopUpdate,
                tb.elementary((UpdateableOperator) anonPermissionsHeapTerm.op(),
                    tb.var(heapLDT.getPermissionHeap())));
        }

        return beforeLoopUpdate;
    }

}
