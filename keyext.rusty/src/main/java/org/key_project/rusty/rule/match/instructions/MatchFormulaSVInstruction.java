/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.match.instructions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElementCursor;
import org.key_project.logic.Term;
import org.key_project.prover.rules.MatchConditions;
import org.key_project.rusty.logic.RustyDLTheory;
import org.key_project.rusty.logic.op.sv.FormulaSV;

import org.jspecify.annotations.NonNull;

public class MatchFormulaSVInstruction extends MatchSchemaVariableInstruction<@NonNull FormulaSV> {

    protected MatchFormulaSVInstruction(FormulaSV op) {
        super(op);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(Term subst, MatchConditions mc, LogicServices services) {
        if (subst.sort() == RustyDLTheory.FORMULA) {
            return addInstantiation(subst, mc, services);
        }
        return null;
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
