/*
 * This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only
 */

/**
 * A language-agnostic framework for taclet find-matching that produces, from a single description
 * of a pattern, both an interpreted matcher (a sequence of
 * {@link org.key_project.prover.rules.matcher.vm.instruction.VMInstruction}s run by
 * {@link org.key_project.prover.rules.matcher.vm.VMProgramInterpreter}) and a cursor-free compiled
 * matcher. It works purely over {@link org.key_project.logic.SyntaxElement} /
 * {@link org.key_project.logic.Term} and the calculus matcher abstractions
 * ({@code MatchResultInfo}, {@code VMInstruction}, {@code MatchProgram}); it depends only on
 * {@code key.ncore}, {@code key.ncore.calculus} and {@code key.util}, never on a
 * language-specific module such as {@code key.core}.
 *
 * <p>
 * The framework has two symmetric halves. For the <b>term skeleton</b> of a find pattern,
 * {@link org.key_project.prover.rules.matcher.compiler.MatchPlan} nodes describe how each subterm
 * is matched ({@code OperatorPlan}, {@code SchemaVarPlan}, with per-operator
 * {@link org.key_project.prover.rules.matcher.compiler.MatchHead}s). For the <b>program</b> inside
 * a modality, {@link org.key_project.prover.rules.matcher.compiler.ProgramMatchPlan} nodes do the
 * same for the program syntax tree ({@code ProgramLeafPlan}, {@code ProgramStructuralPlan},
 * {@code ProgramListSVPlan}, with the child walk in
 * {@link org.key_project.prover.rules.matcher.compiler.ProgramChildSequence}).
 *
 * <p>
 * A language front-end (Java today; other provers analogously) supplies only what is genuinely its
 * own, each piece small:
 * <ul>
 * <li>a <b>dispatch</b> that walks its pattern syntax and composes the plan nodes — one
 * {@code instanceof} case per construct;</li>
 * <li>the <b>match instructions</b> for its schema-variable kinds and special leaves (fed into
 * {@code SchemaVarPlan} / {@code ProgramLeafPlan});</li>
 * <li>{@link org.key_project.prover.rules.matcher.compiler.BinderMatcher} — how its bound
 * variables are bound and unbound;</li>
 * <li>{@link org.key_project.prover.rules.matcher.compiler.ProgramMatchHook} — how the program of
 * a modality is entered from the term skeleton;</li>
 * <li>{@link org.key_project.prover.rules.matcher.compiler.ListSVMatcher} — which program elements
 * a list schema variable may absorb, and how the matched run is recorded;</li>
 * <li>per-operator {@code MatchHead}s and per-construct guards where its calculus has special
 * matching (modalities, updates, parametric functions, ...).</li>
 * </ul>
 * Everything else — the plan skeleton, the child walks, the greedy list-SV run, the emission of
 * interpreter instructions and the compilation to cursor-free matchers — is shared.
 */
package org.key_project.prover.rules.matcher.compiler;
