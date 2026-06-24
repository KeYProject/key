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
public class VMProgramInterpreter implements MatchProgram, ProgramChildrenMatcher {

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
    @Override
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

    /**
     * Executes the program against the children of {@code parent} starting at child index
     * {@code startChild}, i.e. the program is interpreted as a sequence of per-child matchers each
     * consuming exactly one child of {@code parent} (advancing via {@code gotoNextSibling}). This
     * is
     * used to match the active statements of a context block, where matching does not start at the
     * root but at a child offset of the located source element (the equivalent of
     * {@code matchChildren(source, mc, offset)} on the interpreter side).
     * <p>
     * The caller must guarantee that {@code parent} has at least {@code startChild + k} children,
     * where {@code k} is the number of children this program consumes; otherwise the cursor would
     * run past the available children. (The context-block matcher ensures this before calling.)
     *
     * @param parent the element whose children are to be matched
     * @param startChild the index of the first child to match against
     * @param mc the initial match conditions
     * @param services the logic services
     * @return the resulting match conditions, or {@code null} if the match fails
     */
    @Override
    public @Nullable MatchResultInfo matchChildrenFrom(SyntaxElement parent, int startChild,
            MatchResultInfo mc, LogicServices services) {
        if (instruction.length == 0) {
            // nothing to match (empty active-statement block) -> succeed unchanged
            return mc;
        }
        MatchResultInfo result = mc;
        final PoolSyntaxElementCursor navi = PoolSyntaxElementCursor.get(parent);
        navi.gotoNext(); // descend to the first child of parent
        for (int i = 0; i < startChild; i++) {
            navi.gotoNextSibling(); // advance to child number startChild
        }
        int instrPtr = 0;
        while (result != null && instrPtr < instruction.length) {
            result = instruction[instrPtr].match(navi, result, services);
            instrPtr++;
        }
        navi.release();
        return result;
    }
}
