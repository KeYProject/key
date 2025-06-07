/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.op.Operator;

public interface MatchOperatorInstruction extends MatchInstruction {

    MatchConditions match(Operator instantiationCandidate, MatchConditions matchConditions,
            LogicServices services);

}
