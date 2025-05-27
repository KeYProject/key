/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.match.instructions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElementCursor;
import org.key_project.logic.Term;
import org.key_project.prover.rules.instantiation.MatchConditions;
import org.key_project.rusty.logic.op.sv.TermSV;

import org.jspecify.annotations.NonNull;

public class MatchTermSVInstruction extends MatchSchemaVariableInstruction<@NonNull TermSV> {
    protected MatchTermSVInstruction(TermSV op) {
        super(op);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(Term subst, MatchConditions mc, LogicServices services) {
        return addInstantiation(subst, mc, services);
    }

    @Override
    public MatchConditions match(SyntaxElementCursor cursor, MatchConditions mc,
            LogicServices services) {
        final MatchConditions result = match((Term) cursor.getCurrentNode(), mc, services);
        if (result != null) {
            cursor.gotoNextSibling();
        }
        return result;
    }
}
