/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;


import de.uka.ilkd.key.scripts.meta.Argument;
import de.uka.ilkd.key.scripts.meta.Documentation;

import org.checkerframework.checker.nullness.qual.MonotonicNonNull;

/**
 * Sets the behavior if an already closed proof is encountered: Either throw an exception (default
 * behavior, sensible for specially tailored scripts for which a prematurely closed proof is
 * unexpected) or peacefully terminate (if the script addresses different problems of different
 * complexity in a try-and-error manner, etc.).
 *
 * @author Dominic Steinhoefel
 *
 * @deprecated This should be merged in the {@link SetCommand} with a parameter like "failonclosed".
 */
@Deprecated
@Documentation(category = "Control", value = """
        Controls the behavior when a script encounters an already closed proof.

        When set to "on" (default): Throws a `ProofAlreadyClosedException` if a command attempts
        to operate on a closed proof. This is the recommended setting for scripts that expect
        specific proof structures.

        When set to "off": Silently terminates script execution without throwing an exception.
        Useful for generic scripts that may encounter proofs of varying complexity where premature
        closure is acceptable.
        """)
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
        @Documentation(value = "'on' or 'off'. Any other value defaults to 'on'.")
        public @MonotonicNonNull String command;
    }

}
