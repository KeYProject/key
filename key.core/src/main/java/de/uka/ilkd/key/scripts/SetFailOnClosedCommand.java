/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.scripts.meta.Option;

import org.jspecify.annotations.NonNull;

/**
 * Sets the behavior if an already closed proof is encountered: Either throw an exception (default
 * behavior, sensible for specially tailored scripts for which a prematurely closed proof is
 * unexpected) or peacefully terminate (if the script addresses different problems of different
 * complexity in a try-and-error manner, etc.).
 *
 * @author Dominic Steinhoefel
 */
public class SetFailOnClosedCommand extends AbstractCommand<SetFailOnClosedCommand.Parameters> {
    public SetFailOnClosedCommand() {
        super(Parameters.class);
    }

    @Override
    public @NonNull String getName() {
        return "@failonclosed";
    }

    @Override
    public Parameters evaluateArguments(@NonNull EngineState state, Map<String, Object> arguments)
            throws Exception {
        return state.getValueInjector().inject(this, new Parameters(), arguments);
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, @NonNull Parameters args,
            @NonNull EngineState state)
            throws ScriptException, InterruptedException {
        state.setFailOnClosedOn(!"off".equalsIgnoreCase(args.command));
    }

    @SuppressWarnings("initialization")
    public static class Parameters {
        /**
         * The command: "on" or "off". Anything else defaults to "on".
         */
        @Option("#2")
        public String command;
    }

}
