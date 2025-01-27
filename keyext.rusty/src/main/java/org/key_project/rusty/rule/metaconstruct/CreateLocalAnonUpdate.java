/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.metaconstruct;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.TermBuilder;
import org.key_project.rusty.logic.op.AbstractTermTransformer;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.logic.op.RFunction;
import org.key_project.rusty.rule.inst.SVInstantiations;
import org.key_project.rusty.util.MiscTools;
import org.key_project.util.collection.ImmutableSet;

/**
 * Expects a loop body and creates the anonymizing update
 * <code>out_1:=anon_1||...||out_n:=anon_n</code>, where anon_1, ..., anon_n are the written
 * variables in the loop body visible to the outside.
 *
 * @author Dominic Steinhoefel
 */
public class CreateLocalAnonUpdate extends AbstractTermTransformer {
    public CreateLocalAnonUpdate() {
        super(new Name("#createLocalAnonUpdate"), 1);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst, Services services) {
        final Term target = term.sub(0);

        // the target term should have a program block
        if (!(target.op() instanceof Modality mod)) {
            return null;
        }

        final var pe = mod.program().program();

        final ImmutableSet<ProgramVariable> localOuts = MiscTools.getLocalOuts(pe, services);
        return createLocalAnonUpdate(localOuts, services);
    }

    private static Term createLocalAnonUpdate(ImmutableSet<ProgramVariable> localOuts,
            Services services) {
        final TermBuilder tb = services.getTermBuilder();

        Term anonUpdate = tb.skip();
        for (var pv : localOuts) {
            final Function anonFn = anonConstForPV(pv, services);
            final Term upd = tb.elementary(pv, tb.func(anonFn));
            anonUpdate = tb.parallel(anonUpdate, upd);
        }

        return anonUpdate;
    }

    private static Function anonConstForPV(ProgramVariable pv, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final var name = new Name(tb.newName(pv.name().toString()));
        final var fn = new RFunction(name, pv.sort(), true);
        services.getNamespaces().functions().addSafely(fn);

        return fn;
    }
}
