/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.compiler;

import java.util.List;

import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

/**
 * A node of a <em>match plan</em>: a single, language-agnostic description of how to match one
 * (sub)pattern, from which <em>both</em> back-ends are derived.
 *
 * <p>
 * A match plan is built once per find pattern (when the taclet base is loaded) by a per-language
 * dispatch that composes plan nodes for each syntax construct. The point is that each construct is
 * described in exactly one place: a node carries both
 * <ul>
 * <li>{@link #emitInstructions(List)} — the interpreted back-end: it appends the cursor-based
 * {@link VMInstruction}s executed by {@code VMProgramInterpreter}; and</li>
 * <li>{@link #compile()} — the compiled back-end: it builds a cursor-free {@link MatchProgram} that
 * navigates the syntax element directly.</li>
 * </ul>
 * Adding a construct (or fixing its matching) is therefore done once, in the node, and both the
 * interpreter and the compiler stay in sync by construction.
 *
 * <p>
 * Both emissions are produced at plan-construction time, so neither adds runtime overhead over the
 * hand-written matchers they replace: the interpreter still runs a {@code VMInstruction[]} and the
 * compiler still runs the resulting {@link MatchProgram}.
 */
public interface MatchPlan {

    /**
     * Appends, to {@code out}, the {@link VMInstruction}s matching this (sub)pattern for the
     * cursor-based interpreter. The cursor is expected to point at the element to be matched and,
     * on
     * completion of the appended instructions, to have advanced past it (to its next sibling), so
     * that sibling plans can be appended directly after.
     *
     * @param out the instruction list being built
     */
    void emitInstructions(List<VMInstruction> out);

    /**
     * Builds the cursor-free compiled matcher for this (sub)pattern. The returned
     * {@link MatchProgram} is applied to the syntax element to be matched (the same element the
     * interpreter's cursor would point at) and returns the extended match result, or {@code null}
     * on
     * failure.
     *
     * @return the compiled matcher for this plan node
     */
    MatchProgram compile();
}
