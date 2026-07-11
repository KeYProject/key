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
 * program AST with its hand-written per-construct match methods. The current element is the
 * modality's {@link JavaBlock}; the whole program is consumed in this one instruction.
 *
 * <p>
 * This is the legacy counterpart of the single-source program dispatch
 * ({@code JavaProgramMatchPlanBuilder}) and the ultimate safety net of the interpreter back-end:
 * it is used for a program the converted instructions do not cover (conversion off — the default —
 * or a construct outside the dispatch, e.g. a variable-arity list schema variable). It is the main
 * remaining consumer of the AST {@code match} methods and is intended to be removed together with
 * them once the interpreter back-end is retired.
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
