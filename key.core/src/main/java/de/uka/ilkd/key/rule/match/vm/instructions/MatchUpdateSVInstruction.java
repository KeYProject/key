/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public class MatchUpdateSVInstruction extends MatchSchemaVariableInstruction<UpdateSV> {

    protected MatchUpdateSVInstruction(@NonNull UpdateSV op) {
        super(op);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public @Nullable MatchConditions match(@NonNull Term subst, @NonNull MatchConditions mc, @NonNull Services services) {
        return addInstantiation(subst, mc, services);
    }

    @Override
    public @Nullable MatchConditions match(@NonNull TermNavigator termPosition, @NonNull MatchConditions mc,
                                           @NonNull Services services) {
        MatchConditions result = match(termPosition.getCurrentSubterm(), mc, services);
        if (result != null) {
            termPosition.gotoNextSibling();
        }
        return result;
    }

}
