/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.util.collection.ImmutableSet;

/**
 * Expects a loop body and creates the anonymizing update
 * <code>out_1:=anon_1||...||out_n:=anon_n</code>, where anon_1, ..., anon_n are the written
 * variables in the loop body visible to the outside.
 *
 * @author Dominic Steinhoefel
 */
public final class CreateLocalAnonUpdate extends AbstractTermTransformer {

    public CreateLocalAnonUpdate() {
        super(new Name("#createLocalAnonUpdate"), 1);
    }

    @Override
    public JTerm transform(JTerm term, SVInstantiations svInst, Services services) {
        final JTerm target = term.sub(0);

        // the target term should have a Java block
        if (target.javaBlock() == JavaBlock.EMPTY_JAVABLOCK) {
            return null;
        }

        assert target.op() instanceof JModality;

        final ProgramElement pe = target.javaBlock().program();

        assert pe != null;
        assert pe instanceof StatementBlock;

        final ImmutableSet<LocationVariable> localOuts = //
            MiscTools.getLocalOuts(pe, services);
        return createLocalAnonUpdate(localOuts, services);
    }

    private static JTerm createLocalAnonUpdate(ImmutableSet<LocationVariable> localOuts,
            Services services) {
        final TermBuilder tb = services.getTermBuilder();

        JTerm anonUpdate = tb.skip();
        for (var pv : localOuts) {
            final Function anonFunc = anonConstForPV(pv, services);
            final JTerm elemUpd = //
                tb.elementary(pv, tb.func(anonFunc));
            anonUpdate = tb.parallel(anonUpdate, elemUpd);
        }

        return anonUpdate;
    }

    private static Function anonConstForPV(ProgramVariable pv, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Name anonFuncName = new Name(tb.newName(pv.name().toString()));
        final Function anonFunc = new JFunction(anonFuncName, pv.sort(), true);
        services.getNamespaces().functions().addSafely(anonFunc);

        return anonFunc;
    }
}
