/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import java.util.List;

import de.uka.ilkd.key.logic.GenericArgument;
import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ParametricSortInstance;

import org.key_project.logic.Term;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.compiler.MatchHead;
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.getCheckNodeKindInstruction;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.getMatchGenericSortInstruction;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.getMatchIdentityInstruction;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.getSimilarParametricFunctionInstruction;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.gotoNextInstruction;

/**
 * Match head for a {@link ParametricFunctionInstance}: it checks that the operator has the same
 * base and matches the generic arguments (a generic sort, or a concrete argument by identity); the
 * function's subterms are matched by the enclosing
 * {@link org.key_project.prover.rules.matcher.compiler.OperatorPlan}. Mirrors the
 * parametric-function fragments of the hand-written matchers.
 */
public final class ParametricFunctionHead implements MatchHead {

    /** the pattern's parametric function; kept for {@link #toString} only. */
    private final ParametricFunctionInstance pfi;
    private final MatchInstruction similar;
    private final MatchInstruction[] argMatchers;

    private ParametricFunctionHead(ParametricFunctionInstance pfi, MatchInstruction similar,
            MatchInstruction[] argMatchers) {
        this.pfi = pfi;
        this.similar = similar;
        this.argMatchers = argMatchers;
    }

    /**
     * @param pfi the parametric function instance pattern
     * @return a head for {@code pfi}, or {@code null} if a generic argument uses a parametric sort
     *         instance (which the matchers do not handle; then the caller falls back)
     */
    public static @Nullable ParametricFunctionHead of(ParametricFunctionInstance pfi) {
        final int argCount = pfi.getChildCount();
        final MatchInstruction[] argMatchers = new MatchInstruction[argCount];
        for (int i = 0; i < argCount; i++) {
            final GenericArgument arg = (GenericArgument) pfi.getChild(i);
            if (arg.sort() instanceof GenericSort gs) {
                argMatchers[i] = getMatchGenericSortInstruction(gs);
            } else if (arg.sort() instanceof ParametricSortInstance) {
                return null;
            } else {
                argMatchers[i] = getMatchIdentityInstruction(arg);
            }
        }
        return new ParametricFunctionHead(pfi, getSimilarParametricFunctionInstruction(pfi),
            argMatchers);
    }

    @Override
    public void emit(List<VMInstruction> out) {
        out.add(getCheckNodeKindInstruction(ParametricFunctionInstance.class));
        out.add(similar);
        out.add(gotoNextInstruction());
        for (MatchInstruction argMatcher : argMatchers) {
            out.add(argMatcher);
            out.add(gotoNextInstruction());
        }
    }

    @Override
    public MatchProgram compileHeadCheck() {
        final MatchInstruction sim = similar;
        final MatchInstruction[] args = argMatchers;
        return (element, mc, services) -> {
            if (!(((Term) element).op() instanceof ParametricFunctionInstance actualPfi)) {
                return null;
            }
            MatchResultInfo r = sim.match(actualPfi, mc, services);
            for (int i = 0; r != null && i < args.length; i++) {
                r = args[i].match(actualPfi.getChild(i), r, services);
            }
            return r;
        };
    }

    @Override
    public String toString() {
        return "parametric(" + pfi.name() + ")";
    }
}
