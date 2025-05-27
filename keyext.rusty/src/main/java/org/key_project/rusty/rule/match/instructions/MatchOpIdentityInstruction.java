/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.match.instructions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElementCursor;
import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.prover.rules.instantiation.MatchConditions;

/**
 * The match instruction reports a success if the top level operator of the term to be matched is
 * the <strong>same</strong>(identical) operator like the one for which this instruction has been
 * instantiated
 *
 * @param <T> the type of the operator used as template
 */
public class MatchOpIdentityInstruction<T extends Operator> extends Instruction<T>
        implements MatchOperatorInstruction {

    public MatchOpIdentityInstruction(T op) {
        super(op);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final MatchConditions match(Term instantiationCandidate, MatchConditions matchConditions,
            LogicServices services) {
        if (instantiationCandidate.op() == op) {
            return matchConditions;
        }
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(Operator instantiationCandidate, MatchConditions matchConditions,
            LogicServices services) {
        if (instantiationCandidate == op) {
            return matchConditions;
        }
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(SyntaxElementCursor cursor, MatchConditions matchConditions,
            LogicServices services) {
        // TODO: Is there a more suitable place for this?
        // Go to op
        cursor.goToNext();
        MatchConditions result =
            match((Operator) cursor.getCurrentNode(), matchConditions, services);
        if (result != null) {
            cursor.goToNext();
        }
        return result;
    }

}
