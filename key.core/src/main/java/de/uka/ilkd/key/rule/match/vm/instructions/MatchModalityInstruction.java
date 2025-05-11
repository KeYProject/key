/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * The match instruction reports a success if the top level operator of the term to be matched is
 * the <strong>same</strong> modality like the one for which this instruction has been
 * instantiated
 */
public class MatchModalityInstruction extends Instruction<Modality>
        implements MatchOperatorInstruction {

    public MatchModalityInstruction(@NonNull Modality op) {
        super(op);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final MatchConditions match(@NonNull Term t, MatchConditions matchConditions,
                                       Services services) {
        return match(t.op(), matchConditions, services);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public @Nullable MatchConditions match(Operator instantiationCandidate, MatchConditions matchConditions,
                                           Services services) {
        if (instantiationCandidate instanceof Modality mod1 && mod1.kind() == op.kind()) {
            return matchConditions;
        } else {
            return null;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public @Nullable MatchConditions match(@NonNull TermNavigator termPosition, MatchConditions matchConditions,
                                           Services services) {
        return match(termPosition.getCurrentSubterm(), matchConditions, services);
    }

}
