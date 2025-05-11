/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.scripts.meta.Option;

import org.jspecify.annotations.NonNull;

/**
 * A simple "echo" command for giving feedback to human observers during lengthy executions.
 */
public class EchoCommand extends AbstractCommand<EchoCommand.Parameters> {
    public EchoCommand() {
        super(Parameters.class);
    }

    @Override
    public @NonNull String getName() {
        return "echo";
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
        var obs = state.getObserver();
        if (obs != null) {
            obs.accept(new ProofScriptEngine.EchoMessage(args.message));
        }
    }

    @SuppressWarnings("initialization")
    public static class Parameters {
        /**
         * The message to show.
         */
        @Option("#2")
        public String message;
    }

}
