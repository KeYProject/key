/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;


import de.uka.ilkd.key.scripts.meta.Argument;

import de.uka.ilkd.key.scripts.meta.Documentation;
import org.checkerframework.checker.nullness.qual.MonotonicNonNull;

/**
 * An internal command to switch on/off echoing of executed commands.
 */
@Deprecated
@Documentation(category = "Internal", value = """
        An internal command to switch on/off echoing of executed commands.
        """)
public class SetEchoCommand extends AbstractCommand {
    public SetEchoCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "@echo";
    }

    @Override
    public void execute(ScriptCommandAst args)
            throws ScriptException, InterruptedException {
        Parameters parameters = state().getValueInjector().inject(new Parameters(), args);
        state().setEchoOn("on".equalsIgnoreCase(parameters.command));
    }

    public static class Parameters {
        /**
         * The command: "on" or "off". Anything else defaults to "off".
         */
        @Argument
        public @MonotonicNonNull String command;
    }

}
