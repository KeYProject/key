/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceData;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;

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
