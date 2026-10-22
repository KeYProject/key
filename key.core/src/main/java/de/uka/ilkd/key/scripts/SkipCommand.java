/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.scripts.meta.Documentation;

@Documentation(category = "Control", value = "Does exactly nothing.")
public class SkipCommand extends NoArgumentCommand {
    @Override
    public void execute(AbstractUserInterfaceControl uiControl, ScriptCommandAst args,
            EngineState stateMap)
            throws ScriptException, InterruptedException {
    }

    @Override
    public String getName() {
        return "skip";
    }
}
