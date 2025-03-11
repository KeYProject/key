/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;

public class MatchTermSVInstruction extends MatchSchemaVariableInstruction<TermSV> {

    protected MatchTermSVInstruction(TermSV op) {
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
    public MatchConditions match(TermNavigator termPosition, MatchConditions mc,
            Services services) {
        final MatchConditions result = match(termPosition.getCurrentSubterm(), mc, services);
        if (result != null) {
            termPosition.gotoNextSibling();
        }
        return result;
    }

}
