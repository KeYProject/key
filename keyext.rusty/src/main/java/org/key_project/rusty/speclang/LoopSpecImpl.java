/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.speclang;

import java.util.function.UnaryOperator;

import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.expr.LoopExpression;
import org.key_project.rusty.logic.op.ProgramFunction;
import org.key_project.util.collection.ImmutableList;

/**
 * Standard implementation of the LoopInvariant interface.
 */
public final class LoopSpecImpl implements LoopSpecification {
    private final LoopExpression loop;

    private final Term originalInvariant;

    private final Term originalVariant;

    private final ImmutableList<Term> localIns;
    private final ImmutableList<Term> localOuts;

    public LoopSpecImpl(LoopExpression loop, Term invariant, Term variant,
            ImmutableList<Term> localIns, ImmutableList<Term> localOuts) {
        assert loop != null;
        this.loop = loop;
        this.originalInvariant = invariant;
        this.originalVariant = variant;
        this.localIns = localIns;
        this.localOuts = localOuts;
    }

    @Override
    public String getName() {
        return "Loop Invariant";
    }

    @Override
    public String getDisplayName() {
        return "Loop Invariant";
    }

    @Override
    public LoopSpecification map(UnaryOperator<Term> op, Services services) {
        var newLocalIns = localIns.map(op);
        var newLocalOuts = localOuts.map(op);
        return new LoopSpecImpl(loop, op.apply(originalInvariant), op.apply(originalVariant),
            newLocalIns, newLocalOuts);
    }

    @Override
    public LoopExpression getLoop() {
        return loop;
    }

    @Override
    public ProgramFunction getTarget() {
        return null;
    }

    @Override
    public Term getInvariant(Services services) {
        return originalInvariant;
    }

    @Override
    public Term getVariant(Services services) {
        return originalVariant;
    }
}
