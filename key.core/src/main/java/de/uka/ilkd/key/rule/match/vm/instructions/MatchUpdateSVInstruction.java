/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.PoolSyntaxElementCursor;

public class MatchUpdateSVInstruction extends MatchSchemaVariableInstruction {

    protected MatchUpdateSVInstruction(UpdateSV op) {
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
    public MatchConditions match(PoolSyntaxElementCursor cursor, MatchConditions mc,
            LogicServices services) {
        MatchConditions result = match((Term) cursor.getCurrentElement(), mc, services);
        if (result != null) {
            cursor.gotoNextSibling();
        }
        return result;
    }

}
