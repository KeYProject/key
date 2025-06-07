/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;

import org.key_project.logic.LogicServices;
import org.key_project.logic.op.Operator;

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
    public final MatchConditions match(JTerm instantiationCandidate,
            MatchConditions matchConditions,
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
    public MatchConditions match(TermNavigator termPosition, MatchConditions matchConditions,
            LogicServices services) {
        MatchConditions result = match(termPosition.getCurrentSubterm(), matchConditions, services);
        if (result != null) {
            termPosition.gotoNext();
        }
        return result;
    }

}
