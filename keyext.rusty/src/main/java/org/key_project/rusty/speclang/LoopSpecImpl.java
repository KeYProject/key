/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.speclang;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.function.UnaryOperator;

import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.expr.LoopExpression;
import org.key_project.rusty.logic.op.ProgramFunction;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.proof.OpReplacer;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.MapUtil;

/**
 * Standard implementation of the LoopInvariant interface.
 */
public final class LoopSpecImpl implements LoopSpecification {
    private final LoopExpression loop;

    private final Term originalInvariant;

    private final Term originalVariant;

    private final ImmutableList<Term> localIns;
    private final ImmutableList<Term> localOuts;

    /**
     * The mapping of the pre-state variables.
     */
    private final Map<ProgramVariable, Term> originalAtPres;

    public LoopSpecImpl(LoopExpression loop, Term invariant, Term variant,
            ImmutableList<Term> localIns, ImmutableList<Term> localOuts,
            Map<ProgramVariable, Term> atPres) {
        assert loop != null;
        this.loop = loop;
        this.originalInvariant = invariant;
        this.originalVariant = variant;
        this.localIns = localIns;
        this.localOuts = localOuts;
        this.originalAtPres = atPres;
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
        var newAtPres = originalAtPres.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, e -> op.apply(e.getValue())));
        return new LoopSpecImpl(loop, op.apply(originalInvariant), op.apply(originalVariant),
            newLocalIns, newLocalOuts, newAtPres);
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
    public Term getInvariant(Map<ProgramVariable, Term> atPres, Services services) {
        Map<Term, Term> replaceMap = getReplaceMap(atPres);
        var or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalInvariant);
    }

    @Override
    public Term getVariant(Services services) {
        return originalVariant;
    }

    @Override
    public Term getVariant(Map<ProgramVariable, Term> atPres, Services services) {
        Map<Term, Term> replaceMap = getReplaceMap(atPres);
        var or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalVariant);
    }

    public LoopSpecification withInRangePredicates(Services services) {
        var inv = originalInvariant;
        final var tb = services.getTermBuilder();
        for (Term localOut : localOuts) {
            if (localOut.op() instanceof ProgramVariable pv)
                inv = tb.and(inv, tb.reachableValue(pv));
        }
        return new LoopSpecImpl(loop, inv, originalVariant, localIns, localOuts, originalAtPres);
    }

    private Map<Term, Term> getReplaceMap(Map<ProgramVariable, Term> atPres) {
        final Map<Term, Term> result = new LinkedHashMap<>();

        if (atPres != null) {
            for (var entry : originalAtPres.entrySet()) {
                var pv = entry.getKey();
                Term origReplace = entry.getValue();
                Term replace = atPres.get(pv);
                if (replace != null && origReplace != null) {
                    assert replace.sort().equals(origReplace.sort());
                    result.put(origReplace, replace);
                }
            }
        }
        return result;
    }

    @Override
    public Map<ProgramVariable, Term> getInternalAtPres() {
        return new LinkedHashMap<>(originalAtPres);
    }
}
