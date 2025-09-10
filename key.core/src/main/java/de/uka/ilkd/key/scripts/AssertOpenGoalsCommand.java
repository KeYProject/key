/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;


import de.uka.ilkd.key.scripts.meta.Documentation;
import de.uka.ilkd.key.scripts.meta.Option;

/**
 * Halts the script if the expected number of open and enabled goals is not met.
 * <p>
 * See exported documentation at {@link Parameters} at the end of this file.
 *
 * @author lanzinger
 */
public class AssertOpenGoalsCommand extends AbstractCommand {

    /**
     * Instantiates a new assert command.
     */
    public AssertOpenGoalsCommand() {
        super(Parameters.class);
    }

    @Override
    public void execute(ScriptCommandAst arguments) throws ScriptException, InterruptedException {
        var args = state().getValueInjector().inject(new Parameters(), arguments);

        if (args.goals == null) {
            throw new ScriptException("No parameter specified!");
        }

        if (state().getProof().openEnabledGoals().size() != args.goals) {
            throw new ScriptException("Assertion failed: number of open goals is "
                + state().getProof().openGoals().size() + ", but should be " + args.goals);
        }
    }

    @Override
    public String getName() {
        return "assertOpenGoals";
    }

    /**
     * The Assigned parameters (currently only the passed goals).
     */
    @Documentation("""
            The assert command checks if the number of open and enabled goals is equal to the given number.
            If not, the script is halted with an error message.

            Note: This command was called "assert" originally.
            """)
    public static class Parameters {
        /**
         * The number of open and enabled goals.
         */
        @Option("goals")
        public Integer goals;
    }
}
