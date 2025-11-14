/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;


import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.scripts.meta.Documentation;

@Documentation(category = "Control", value = """
        Exits the currently running script context unconditionally.
        (In the future, there may try-catch blocks to react to this).
        """)
public class ExitCommand extends NoArgumentCommand {
    @Override
    public void execute(AbstractUserInterfaceControl uiControl, ScriptCommandAst args,
            EngineState stateMap)
            throws ScriptException, InterruptedException {
        throw new InterruptedException("Interruption requested from within script");
    }

    @Override
    public String getName() {
        return "exit";
    }
}
