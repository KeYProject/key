/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.rule.MatchConditions;

public interface MatchOperatorInstruction extends MatchInstruction {

    public MatchConditions match(Operator instantiationCandidate, MatchConditions matchConditions,
            Services services);

}
