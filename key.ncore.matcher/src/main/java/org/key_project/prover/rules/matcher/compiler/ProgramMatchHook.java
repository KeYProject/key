/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.compiler;

import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

/**
 * Language SPI for matching the <em>program</em> carried by a modality (the {@code \<{ ... }\>} of
 * a symbolic-execution taclet). This is the second of the two axes on which the Java/Rust/Solidity
 * front-ends differ (the first is {@link BinderMatcher}): each has its own program AST -- Java's
 * {@code JavaBlock}/{@code ContextStatementBlock}, Rust's {@code RustyBlock}, Solidity's block --
 * but all are {@link org.key_project.logic.SyntaxElement}s navigated through {@code getChild}.
 *
 * <p>
 * A hook is built per modality pattern (it captures that pattern's program) and exposes the program
 * matcher for both back-ends. On the interpreter side it is a single {@link VMInstruction} run with
 * the cursor positioned at the program block; on the compiled side it is a {@link MatchProgram}
 * applied directly to the source program block. Both consume exactly one element (the block), so
 * the enclosing modality head can advance to the post-condition subterm afterwards.
 *
 * <p>
 * The framework owns the surrounding modality skeleton (check the modality, match its kind, then
 * the program, then recurse the subterms); a language plugs in only the divergent program matching
 * here. Java additionally has the rich {@code ContextStatementBlock} prefix/suffix machinery, which
 * is entirely encapsulated behind this hook; Rust and Solidity supply their own simpler block
 * matchers.
 */
public interface ProgramMatchHook {

    /**
     * The interpreter instruction matching the modality's program. On entry the cursor points at
     * the source program block; it consumes that block.
     *
     * @return the program-matching instruction
     */
    VMInstruction programInstruction();

    /**
     * The compiled matcher for the modality's program, applied directly to the source program
     * block.
     *
     * @return the compiled program matcher
     */
    MatchProgram compileProgram();
}
