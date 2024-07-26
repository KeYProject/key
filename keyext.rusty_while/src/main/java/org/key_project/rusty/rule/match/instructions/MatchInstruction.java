/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.match.instructions;

import org.key_project.logic.SyntaxElementCursor;
import org.key_project.rusty.Services;
import org.key_project.rusty.rule.MatchConditions;

/**
 * Interface that has to be implemented by instructions for the matching virtual machine
 */
public interface MatchInstruction {
    MatchConditions match(SyntaxElementCursor cursor, MatchConditions matchConditions,
            Services services);
}
