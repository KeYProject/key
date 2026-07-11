/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ContextStatementBlock;
import de.uka.ilkd.key.java.ast.SourceData;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.VMProgramInterpreter;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;

import org.jspecify.annotations.Nullable;

/**
 * Matches the Java program of a modality whose program is a {@link ContextStatementBlock} (the
 * {@code .. ... } pattern that is ubiquitous in symbolic-execution taclets). The intricate context
 * bookkeeping (variable-length prefix descent, inner execution context, prefix/suffix positions)
 * is still performed by {@link ContextStatementBlock#match}; only the matching of the active
 * statements is delegated to the supplied VM sub-program, replacing the monolithic
 * {@code MatchProgramInstruction} for that subtree. The current element is the modality's
 * {@link JavaBlock} (as for {@code MatchProgramInstruction}).
 *
 * @see ContextStatementBlock#match(SourceData, MatchConditions, VMProgramInterpreter)
 */
public final class MatchContextStatementBlockInstruction implements MatchInstruction {

    private final ContextStatementBlock contextBlock;
    private final VMProgramInterpreter activeStatements;

    public MatchContextStatementBlockInstruction(ContextStatementBlock contextBlock,
            VMProgramInterpreter activeStatements) {
        this.contextBlock = contextBlock;
        this.activeStatements = activeStatements;
    }

    @Override
    public @Nullable MatchResultInfo match(SyntaxElement actualElement,
            MatchResultInfo matchConditions, LogicServices services) {
        return contextBlock.match(
            new SourceData(((JavaBlock) actualElement).program(), -1, (Services) services),
            (MatchConditions) matchConditions, activeStatements);
    }
}
