/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.scripts.meta.Documentation;

/**
 * Command for re-activating the first open (not necessarily enabled) {@link Goal} after a "leave"
 * command. Can be useful for complicated proofs where "tryclose" should not apply on certain
 * branches temporarily, but where one still wants to finish the proof.
 *
 * @author Dominic Steinhoefel
 */
@Documentation(category = "Control", value = """
        Reactivates the first open (not necessarily enabled) goal.
        This can be useful after a 'leave' command to continue
        working on a complicated proof where 'tryclose' should not
        apply on certain branches temporarily, but where one still
        wants to finish the proof.""")
public class ActivateCommand extends NoArgumentCommand {
    @Override
    public String getName() {
        return "activate";
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, ScriptCommandAst args,
            EngineState state)
            throws ScriptException, InterruptedException {
        Goal goal = state.getFirstOpenGoal(false);
        goal.setEnabled(true);
    }

}
