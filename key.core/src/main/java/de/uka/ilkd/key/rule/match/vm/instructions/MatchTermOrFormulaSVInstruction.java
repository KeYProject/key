/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.OperatorSV;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.PoolSyntaxElementCursor;

public class MatchTermOrFormulaSVInstruction extends MatchSchemaVariableInstruction {

    protected MatchTermOrFormulaSVInstruction(OperatorSV op) {
        super(op);
        assert op instanceof TermSV || op instanceof FormulaSV;
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
        final MatchConditions result = match((Term) cursor.getCurrentElement(), mc, services);
        if (result != null) {
            cursor.gotoNextSibling();
        }
        return result;
    }

}
