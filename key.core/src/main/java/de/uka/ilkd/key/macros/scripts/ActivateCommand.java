/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.proof.Goal;

/**
 * Command for re-activating the first open (not necessarily enabled) {@link Goal} after a "leave"
 * command. Can be useful for complicated proofs where "tryclose" should not apply on certain
 * branches temporarily, but where one still wants to finish the proof.
 *
 * @author Dominic Steinhoefel
 */
public class ActivateCommand extends NoArgumentCommand {
    @Override
    public String getName() {
        return "activate";
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Void args, EngineState state)
            throws ScriptException, InterruptedException {
        Goal goal = state.getFirstOpenGoal(false);
        goal.setEnabled(true);
    }

}
