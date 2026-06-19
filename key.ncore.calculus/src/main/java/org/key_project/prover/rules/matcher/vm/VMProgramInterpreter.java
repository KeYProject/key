/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.vm;

import org.key_project.logic.LogicServices;
import org.key_project.logic.PoolSyntaxElementCursor;
import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

import org.jspecify.annotations.Nullable;


/**
 * Interpreter for executing a sequence of instructions in a virtual machine
 * designed for matching logical syntax elements.
 * <p>
 * This class interprets a program consisting of {@link VMInstruction}
 * instances, which operate over a {@link SyntaxElement}. The interpreter processes
 * the instructions sequentially and attempts to match the input term against
 * a pattern term under specified match conditions.
 * <p>
 * To execute the program, use the {@link #match(SyntaxElement, MatchResultInfo, LogicServices)}
 * method. It returns the result of the match, which may include additional
 * constraints such as variable instantiations if successful, or {@code null}
 * if the match fails.
 */
public class VMProgramInterpreter {

    /**
     * The sequence of instructions to be executed.
     */
    protected final VMInstruction[] instruction;

    public VMProgramInterpreter(VMInstruction[] instruction) {
        this.instruction = instruction;
    }


    /**
     * Executes the program to attempt matching the given syntax element
     * under the provided match conditions.
     * <p>
     * The interpreter uses a cursor to navigate the structure of the syntax element.
     * If the match succeeds, a {@link MatchResultInfo} object is returned, possibly
     * extending the input conditions with new schema variable instantiations and other
     * constraints (like generic sort instantiations).
     * If any instruction fails to match, the process is aborted and {@code null} is returned.
     *
     * @param toMatch the {@link SyntaxElement} to be matched
     * @param mc the initial {@link MatchResultInfo} containing preconditions for matching;
     *        can be extended during execution
     * @param services the {@link LogicServices} instance providing logic-related utilities
     * @return a {@link MatchResultInfo} containing the result of the match,
     *         or {@code null} if no match was possible
     */
    public @Nullable MatchResultInfo match(SyntaxElement toMatch, MatchResultInfo mc,
            LogicServices services) {
        MatchResultInfo result = mc;
        final PoolSyntaxElementCursor navi = PoolSyntaxElementCursor.get(toMatch);
        int instrPtr = 0;
        while (result != null && instrPtr < instruction.length) {
            result = instruction[instrPtr].match(navi, result, services);
            instrPtr++;
        }
        navi.release();
        return result;
    }
}
