/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.compiler.ListSVMatcher;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.Nullable;

/**
 * Java-DL implementation of the {@link ListSVMatcher} SPI: a source child may join a list schema
 * variable's run if it is admissible for the schema variable's sort
 * ({@code ProgramSVSort.canStandFor}, judged in the execution context recorded with the
 * instantiations), and the collected run is stored as an {@code ImmutableArray} of program
 * elements — or, if the schema variable is already bound, the match succeeds without change
 * exactly when the existing list equals the run. (The interpreter back-end matches list schema
 * variables with {@code ProgramSV.matchListSV}; both must yield identical results.)
 */
public final class JavaListSVMatcher implements ListSVMatcher {

    /** stateless; a single shared instance suffices. */
    public static final JavaListSVMatcher INSTANCE = new JavaListSVMatcher();

    /** the instantiation of a list schema variable that matched no source children */
    private static final ImmutableArray<ProgramElement> EMPTY_LIST_INSTANTIATION =
        new ImmutableArray<>(new ProgramElement[0]);

    private JavaListSVMatcher() {}

    @Override
    public boolean isAdmissible(SchemaVariable listSV, SyntaxElement element, MatchResultInfo mc,
            LogicServices services) {
        final ExecutionContext ec =
            ((MatchConditions) mc).getInstantiations().getExecutionContext();
        return ((ProgramSVSort) ((ProgramSV) listSV).sort()).canStandFor((ProgramElement) element,
            ec, (Services) services);
    }

    @Override
    public @Nullable MatchResultInfo bindRun(SchemaVariable listSV,
            List<? extends SyntaxElement> run, MatchResultInfo mc, LogicServices services) {
        final ImmutableArray<ProgramElement> list = run.isEmpty() ? EMPTY_LIST_INSTANTIATION
                : new ImmutableArray<>(run.toArray(new ProgramElement[0]));
        final MatchConditions matchCond = (MatchConditions) mc;
        SVInstantiations insts = matchCond.getInstantiations();
        final ImmutableArray<ProgramElement> pl = insts.getInstantiation(listSV);
        if (pl != null) {
            return pl.equals(list) ? matchCond : null;
        }
        insts = insts.add(listSV, list, ProgramElement.class, services);
        return insts == null ? null : matchCond.setInstantiations(insts);
    }
}
