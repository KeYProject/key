/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;


import de.uka.ilkd.key.scripts.meta.Option;

/**
 * Halts the script if some condition is not met.
 *
 * @author lanzinger
 */
public class AssertCommand extends AbstractCommand {

    /**
     * Instantiates a new assert command.
     */
    public AssertCommand() {
        super(Parameters.class);
    }

    @Override
    public void execute(ScriptCommandAst arguments) throws ScriptException, InterruptedException {
        var args = state().getValueInjector().inject(this, new Parameters(), arguments);

        if (args.goals == null) {
            throw new ScriptException("No parameter specified!");
        }

        if (state().getProof().openEnabledGoals().size() != args.goals) {
            throw new ScriptException("Assertion failed: number of open goals is "
                + state.getProof().openGoals().size() + ", but should be " + args.goals);
        }
    }

    @Override
    public String getName() {
        return "assert";
    }

    /**
     * The Assigned parameters (currently only the passed goals).
     */
    public static class Parameters {
        /**
         * The number of open and enabled goals.
         */
        @Option("goals")
        public Integer goals;
    }
}
