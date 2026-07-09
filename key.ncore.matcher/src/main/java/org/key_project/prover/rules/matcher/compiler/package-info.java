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
 * matcher.
 *
 * <p>
 * It works purely over {@link org.key_project.logic.SyntaxElement} /
 * {@link org.key_project.logic.Term} and the calculus matcher abstractions
 * ({@code MatchResultInfo}, {@code VMInstruction}, {@code MatchProgram}); it depends only on
 * {@code key.ncore}, {@code key.ncore.calculus} and {@code key.util}, never on the Java-DL
 * specific {@code key.core}. Language-specific behaviour (the concrete syntax constructs, the
 * program/AST sub-matching and the binding of bound variables) is supplied through small SPIs so
 * that the Java, Rust and Solidity front-ends can share this core and only add their own
 * constructs.
 */
package org.key_project.prover.rules.matcher.compiler;
