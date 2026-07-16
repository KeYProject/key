/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.compiler;

import java.util.Arrays;
import java.util.List;

import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.GotoNextInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.MatchProgramElementInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

import org.jspecify.annotations.Nullable;

/**
 * The structural program match, used for every element without special matching behaviour: the
 * source must have the same concrete class as the pattern, pass the optional {@code guard} (an
 * extra scalar field check a language may add, e.g. array dimensions), and its children must match
 * the child plans. The child plans are built by the language front-end's dispatch and passed in.
 * Two child shapes exist:
 * <ul>
 * <li><b>fixed arity</b> (no list-SV child): the source must also have the same child count
 * (both back-ends share the one {@link MatchProgramElementInstruction} checking class + count)
 * and child {@code i} matches source child {@code i} directly, no cursor;</li>
 * <li><b>variable arity</b> (some child is a {@link ProgramListSVPlan}): a cursor walks the
 * source children ({@link ProgramChildSequence}) because a list SV consumes a run of them, and
 * the block size is checked at the end instead of up front. Not interpretable (see
 * {@link ProgramListSVPlan}), so only {@link #compile} is ever exercised for this shape.</li>
 * </ul>
 */
public final class ProgramStructuralPlan implements ProgramMatchPlan {

    private final Class<? extends SyntaxElement> kind;
    /** class + child-count check shared verbatim by {@link #emit} and the fixed-arity step. */
    private final MatchProgramElementInstruction head;
    /** extra scalar field check on the source element, or {@code null} for none. */
    private final @Nullable MatchInstruction guard;
    private final ProgramMatchPlan[] children;
    private final ListSVMatcher listSVMatcher;
    private final boolean varArity;
    private final boolean interpretable;

    /**
     * @param pattern the pattern element (only its class and child count enter the match)
     * @param guard an extra check on the source element, or {@code null} for a plain structural
     *        match
     * @param children one plan per pattern child, built by the front-end's dispatch
     * @param listSVMatcher the language's list-SV judgements (used only if a child is a list SV)
     */
    public ProgramStructuralPlan(SyntaxElement pattern, @Nullable MatchInstruction guard,
            ProgramMatchPlan[] children, ListSVMatcher listSVMatcher) {
        this.kind = pattern.getClass();
        this.head = new MatchProgramElementInstruction(kind, children.length);
        this.guard = guard;
        this.children = children;
        this.listSVMatcher = listSVMatcher;
        boolean varArity = false;
        boolean interpretable = true;
        for (final ProgramMatchPlan child : children) {
            varArity |= child.listSV() != null;
            interpretable &= child.interpretable();
        }
        this.varArity = varArity;
        this.interpretable = interpretable;
    }

    @Override
    public boolean interpretable() {
        return interpretable;
    }

    @Override
    public void emit(List<VMInstruction> out) {
        out.add(head);
        if (guard != null) {
            out.add(guard);
        }
        out.add(GotoNextInstruction.INSTANCE);
        for (final ProgramMatchPlan child : children) {
            child.emit(out);
        }
    }

    @Override
    public MatchProgram compile() {
        if (!varArity) {
            final MatchProgram[] compiledChildren = new MatchProgram[children.length];
            for (int i = 0; i < children.length; i++) {
                compiledChildren[i] = children[i].compile();
            }
            return (actual, mc, services) -> {
                MatchResultInfo r = head.match(actual, mc, services);
                if (r == null) {
                    return null;
                }
                if (guard != null) {
                    r = guard.match(actual, r, services);
                    if (r == null) {
                        return null;
                    }
                }
                return ProgramChildSequence.matchOneToOne(compiledChildren, actual, r, services);
            };
        }
        // a list-SV child consumes a variable-length run of source children, so the head's
        // child-count check cannot be applied up front: check the class only, walk the source
        // children with a cursor, and require it to end exactly after the last child.
        final ProgramChildSequence sequence = ProgramChildSequence.compile(children, listSVMatcher);
        return (actual, mc, services) -> {
            if (actual.getClass() != kind) {
                return null;
            }
            MatchResultInfo r = mc;
            if (guard != null) {
                r = guard.match(actual, r, services);
                if (r == null) {
                    return null;
                }
            }
            // 0: the cursor starts at the parent's first child
            final ProgramChildCursor source = new ProgramChildCursor(actual, 0);
            r = sequence.match(source, r, services);
            if (r == null || source.getChildPos() != actual.getChildCount()) {
                return null;
            }
            return r;
        };
    }

    @Override
    public String toString() {
        return "structural(" + kind.getSimpleName() + (guard != null ? "+guard" : "")
            + (children.length == 0 ? "" : ", " + Arrays.toString(children)) + ")";
    }
}
