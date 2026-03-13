/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;


import de.uka.ilkd.key.scripts.meta.Argument;

import org.checkerframework.checker.nullness.qual.MonotonicNonNull;

/**
 * A simple "echo" command for giving feedback to human observers during lengthy executions.
 */
public class EchoCommand extends AbstractCommand {
    public EchoCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "echo";
    }

    @Override
    public void execute(ScriptCommandAst args)
            throws ScriptException, InterruptedException {
        var params = state().getValueInjector().inject(new Parameters(), args);

        var obs = state().getObserver();
        if (obs != null) {
            obs.accept(new ProofScriptEngine.EchoMessage(params.message));
        }
    }

    public static class Parameters {
        /**
         * The message to show.
         */
        @Argument
        public @MonotonicNonNull String message;
    }

}
