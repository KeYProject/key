/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.SourceData;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;

/**
 * The <em>monolithic</em> program matcher: matches the Java program of a modality by delegating to
 * the pattern's own {@code ProgramElement.match(SourceData, MatchConditions)}, which walks the
 * program AST with the per-construct {@code match} methods of the AST classes. The current element
 * is the modality's {@link JavaBlock}; the whole program is consumed in this one instruction.
 *
 * <p>
 * It is the safety net of the interpreter back-end: it matches a program the converted
 * instructions do not cover (conversion off, the default, or a construct outside the
 * single-source dispatch, e.g. a variable-arity list schema variable), and it is the main consumer
 * of the AST {@code match} methods.
 */
public class MatchProgramInstruction implements MatchInstruction {

    private final ProgramElement pe;

    public MatchProgramInstruction(ProgramElement pe) {
        this.pe = pe;
    }

    @Override
    public MatchResultInfo match(SyntaxElement actualElement, MatchResultInfo matchConditions,
            LogicServices services) {
        final MatchConditions result = pe.match(
            new SourceData(((JavaBlock) actualElement).program(), -1,
                (Services) services),
            (MatchConditions) matchConditions);
        return result;
    }
}
