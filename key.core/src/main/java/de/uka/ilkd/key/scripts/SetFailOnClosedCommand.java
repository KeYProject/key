/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;


import de.uka.ilkd.key.scripts.meta.Argument;

import org.checkerframework.checker.nullness.qual.MonotonicNonNull;

/**
 * Sets the behavior if an already closed proof is encountered: Either throw an exception (default
 * behavior, sensible for specially tailored scripts for which a prematurely closed proof is
 * unexpected) or peacefully terminate (if the script addresses different problems of different
 * complexity in a try-and-error manner, etc.).
 *
 * @author Dominic Steinhoefel
 */
public class SetFailOnClosedCommand extends AbstractCommand {
    public SetFailOnClosedCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "failonclosed";
    }



    @Override
    public void execute(ScriptCommandAst arguments)
            throws ScriptException, InterruptedException {
        var args = state().getValueInjector().inject(new Parameters(), arguments);
        state().setFailOnClosedOn(!"off".equalsIgnoreCase(args.command));
    }

    public static class Parameters {
        /**
         * The command: "on" or "off". Anything else defaults to "on".
         */
        @Argument
        public @MonotonicNonNull String command;
    }

}
