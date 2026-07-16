/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.compiler;

import java.util.List;

import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

import org.jspecify.annotations.Nullable;

/**
 * The single description of how one program (sub)element of a modality is matched, from which both
 * matcher back-ends are derived: {@link #emit} produces the cursor-based interpreter
 * {@link VMInstruction}s and {@link #compile} produces the cursor-free compiled
 * {@link MatchProgram} (direct {@code getChild(i)} navigation). It is the program-AST counterpart
 * of {@link MatchPlan} for terms: a construct is described once, in a language front-end's
 * dispatch, and both back-ends follow that one description.
 *
 * <p>
 * "Advance responsibility" follows the same convention in both back-ends: a plan's interpreter
 * instructions leave the source cursor past the element they consumed (one position for the
 * ordinary one-to-one constructs; a variable number for a list schema variable), and its compiled
 * step navigates the corresponding child positions itself.
 */
public interface ProgramMatchPlan {

    /**
     * Appends the interpreter instructions matching this element (and, for a non-terminal, its
     * child sub-plans) to {@code out}.
     */
    void emit(List<VMInstruction> out);

    /**
     * Called at most once per plan, when the enclosing taclet's matcher is constructed; it may
     * allocate (e.g. pre-compile the child plans) and its result is not memoized.
     *
     * @return the cursor-free compiled matcher for this element, applied directly to the source
     *         program (sub)element (not the enclosing program block).
     */
    MatchProgram compile();

    /**
     * @return the list program schema variable if this plan matches a variable-arity list SV
     *         ({@code #slist}, ...), otherwise {@code null}. A list SV is not matched as an
     *         ordinary one-to-one child: its enclosing element consumes a greedy run of source
     *         children for it (see {@link ProgramChildSequence}), so a parent inspects this to
     *         drive a cursor-walking child match instead of the fixed {@code getChild(i)} one.
     */
    default @Nullable SchemaVariable listSV() {
        return null;
    }

    /**
     * @return whether this plan can be realised on the <em>interpreter</em> (VM-instruction)
     *         back-end. The DFS cursor of the interpreter has no clean end-of-children boundary,
     *         so a variable-arity list SV (matched only on the compiled back-end, by the
     *         enclosing plan's greedy list match) is not interpretable; an element containing one
     *         propagates that. When {@code false} the interpreter side keeps its own matcher for
     *         the whole program, while the compiled side still uses this plan. This is the one
     *         deliberate point where the two back-ends may diverge.
     */
    default boolean interpretable() {
        return true;
    }
}
