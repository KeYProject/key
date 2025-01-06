/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.match.instructions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElementCursor;
import org.key_project.prover.rules.MatchConditions;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.SourceData;
import org.key_project.rusty.logic.RustyBlock;

public class MatchProgramInstruction implements MatchInstruction {

    private final RustyProgramElement pe;

    public MatchProgramInstruction(RustyProgramElement pe) {
        this.pe = pe;
    }

    @Override
    public MatchConditions match(SyntaxElementCursor cursor, MatchConditions matchConditions,
            LogicServices services) {
        final var rb = (RustyBlock) cursor.getCurrentNode();
        final MatchConditions result = pe.match(
            new SourceData(rb.program(), -1, (Services) services),
                (org.key_project.rusty.rule.MatchConditions) matchConditions);
        if (result != null) {
            // TODO: Should the cursor be advanced by the match in the PEs?
            cursor.gotoParent();
            cursor.gotoNextSibling();
        }
        return result;
    }
}
