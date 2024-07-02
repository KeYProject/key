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

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.MiscTools;

/**
 * Creates the wellformedness condition for the given anonymizing heap terms if
 * they apply for the current profile and modality type. At least generates the
 * "wellFormed(anon_heap_LOOP)" condition for the anonymized standard heap.
 *
 * @author Dominic Steinhoefel
 */
public final class CreateWellformedCond extends AbstractTermTransformer {

    public CreateWellformedCond() {
        super(new Name("#wellFormedCond"), 4);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst, Services services) {
        final Term anonHeapTerm = term.sub(1);
        final Term anonSavedHeapTerm = term.sub(2);
        final Term anonPermissionsHeapTerm = term.sub(3);

        final Operator op = term.sub(0).op();
        assert op instanceof Modality;

        return createWellformedCond(MiscTools.isTransaction((Modality) op),
                MiscTools.isPermissions(services), anonHeapTerm,
                anonSavedHeapTerm, anonPermissionsHeapTerm, services);
    }

    /**
     * Creates a wellformedness condition containing the applicable heaps.
     *
     * @param isTransaction
     *            Signals a transaction modality.
     * @param isPermissions
     *            Signals the permission profile.
     * @param anonHeapTerm
     *            The Skolem term for the standard heap.
     * @param anonSavedHeapTerm
     *            The Skolem term for the saved (transaction) heap.
     * @param anonPermissionsHeapTerm
     *            The Skolem term for the permissions heap.
     * @param services
     *            The {@link Services} object.
     * @return The wellformedness condition.
     */
    private Term createWellformedCond(boolean isTransaction,
            boolean isPermissions, Term anonHeapTerm, Term anonSavedHeapTerm,
            Term anonPermissionsHeapTerm, Services services) {
        final TermBuilder tb = services.getTermBuilder();

        Term result = tb.label(tb.wellFormed(anonHeapTerm),
                ParameterlessTermLabel.ANON_HEAP_LABEL);

        if (isTransaction) {
            result = tb.and(result, tb.wellFormed(anonSavedHeapTerm));
        }

        if (isPermissions) {
            result = tb.and(result, tb.wellFormed(anonPermissionsHeapTerm));
        }

        return result;
    }
}