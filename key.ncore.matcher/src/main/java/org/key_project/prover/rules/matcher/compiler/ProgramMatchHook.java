/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.compiler;

import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

/**
 * Language SPI (service provider interface) for matching the <em>program</em> carried by a
 * modality (the {@code \<{ ... }\>} of
 * a symbolic-execution taclet). Each front-end has its own program AST; every program is a
 * {@link org.key_project.logic.SyntaxElement} navigated through {@code getChild}, but which
 * constructs exist and how they match is the language's own.
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
 * the program, then recurse the subterms); a language plugs in only its program matching here.
 * Everything specific to a language's blocks -- including machinery as involved as a context
 * block's prefix/suffix bookkeeping -- stays behind this hook.
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
