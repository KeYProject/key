/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.match.instructions;

import org.key_project.logic.op.Operator;
import org.key_project.rusty.Services;
import org.key_project.rusty.rule.MatchConditions;

public interface MatchOperatorInstruction extends MatchInstruction {

    MatchConditions match(Operator instantiationCandidate, MatchConditions matchConditions,
            Services services);

}
