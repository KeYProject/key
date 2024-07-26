/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.match.instructions;

import org.key_project.logic.SyntaxElementCursor;
import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.sv.UpdateSV;
import org.key_project.rusty.rule.MatchConditions;

import org.jspecify.annotations.NonNull;

public class MatchUpdateSVInstruction extends MatchSchemaVariableInstruction<@NonNull UpdateSV> {
    protected MatchUpdateSVInstruction(UpdateSV op) {
        super(op);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(Term subst, MatchConditions mc, Services services) {
        return addInstantiation(subst, mc, services);
    }

    @Override
    public MatchConditions match(SyntaxElementCursor cursor, MatchConditions mc,
            Services services) {
        MatchConditions result = match((Term) cursor.getCurrentNode(), mc, services);
        if (result != null) {
            cursor.gotoNextSibling();
        }
        return result;
    }

}
