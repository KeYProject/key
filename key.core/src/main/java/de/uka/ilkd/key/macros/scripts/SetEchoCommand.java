/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.macros.scripts.meta.Option;

/**
 * A simple "echo" command for giving feedback to human observers during lengthy executions.
 */
public class SetEchoCommand extends AbstractCommand<SetEchoCommand.Parameters> {
    public SetEchoCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "@echo";
    }

    @Override
    public Parameters evaluateArguments(EngineState state, Map<String, String> arguments)
            throws Exception {
        return state.getValueInjector().inject(this, new Parameters(), arguments);
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Parameters args, EngineState state)
            throws ScriptException, InterruptedException {
        state.setEchoOn("on".equalsIgnoreCase(args.command));
    }

    public static class Parameters {
        /**
         * The command: "on" or "off". Anything else defaults to "off".
         */
        @Option("#2")
        public String command;
    }

}
