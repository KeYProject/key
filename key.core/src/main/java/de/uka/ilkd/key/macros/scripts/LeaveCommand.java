/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.macros.scripts;

import java.util.logging.Logger;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.proof.Goal;

public class LeaveCommand extends NoArgumentCommand {
    private static Logger log = Logger.getLogger(ProofScriptCommand.class.getName());


    @Override
    public String getName() {
        return "leave";
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl,
            Void args, EngineState state) throws ScriptException, InterruptedException {
        Goal goal = state.getFirstOpenAutomaticGoal();
        log.info("Deactivating " + goal.node().serialNr());
        goal.setEnabled(false);
    }

}
