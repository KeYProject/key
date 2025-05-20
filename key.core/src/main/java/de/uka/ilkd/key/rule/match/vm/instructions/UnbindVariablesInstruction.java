/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;

import org.jspecify.annotations.NonNull;

public class UnbindVariablesInstruction implements MatchInstruction {

    @Override
    public @NonNull MatchConditions match(TermNavigator termPosition,
            @NonNull MatchConditions matchConditions,
            Services services) {
        return matchConditions.shrinkRenameTable();
    }

}
