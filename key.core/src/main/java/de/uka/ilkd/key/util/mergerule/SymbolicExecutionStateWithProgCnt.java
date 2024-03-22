/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.mergerule;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * A symbolic execution state with program counter is a triple of a symbolic state in form of a
 * parallel update, a path condition in form of a JavaDL formula, and a program counter in form of a
 * JavaDL formula with non-empty Java Block (and a possible post condition as first, and only, sub
 * term).
 *
 * @param symbolicState     The symbolic state (parallel update).
 * @param pathCondition     The path condition (formula).
 * @param programCounter    The program counter: Formula with non-empty Java block and post
 *                          condition as only sub term.
 * @param correspondingNode The node corresponding to this SE state.
 * @author Dominic Scheurer
 */
@NullMarked
public record SymbolicExecutionStateWithProgCnt(Term symbolicState, Term pathCondition,
                                                Term programCounter, @Nullable Node correspondingNode) {
    /**
     * @return The corresponding SE state (without the program counter).
     */
    public SymbolicExecutionState toSymbolicExecutionState() {
        return new SymbolicExecutionState(symbolicState, pathCondition, correspondingNode);
    }
}
