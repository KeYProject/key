/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.OperatorSV;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.PoolSyntaxElementCursor;

/**
 * Matching VM instruction that matches all operator schema variables that
 * are not a {@link VariableSV} or a {@link ProgramSV}.
 * For those see {@link MatchVariableSVInstruction} and {@link MatchProgramSVInstruction}.
 */
public class MatchNonVariableSVInstruction extends MatchSchemaVariableInstruction {

    protected MatchNonVariableSVInstruction(OperatorSV op) {
        super(op);
        assert !(op instanceof VariableSV || op instanceof ProgramSV);
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
        return match((Term) cursor.getCurrentElement(), mc, services);
    }

}
