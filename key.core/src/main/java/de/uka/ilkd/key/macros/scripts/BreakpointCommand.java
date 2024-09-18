/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import de.uka.ilkd.key.macros.scripts.meta.Option;

/**
 * Halts the script if some condition is not met.
 *
 * @author lanzinger
 */
public class BreakpointCommand extends AbstractCommand<BreakpointCommand.Parameters> {

    /**
     * Instantiates a new assert command.
     */
    public BreakpointCommand() {
        super(Parameters.class);
    }

    @Override
    public Parameters evaluateArguments(EngineState state,
            Map<String, String> arguments) throws Exception {
        return state.getValueInjector().inject(this, new Parameters(),
            arguments);
    }

    @Override
    public void execute(Parameters args)
            throws ScriptException, InterruptedException {
        if (args.goals == null) {
            throw new ScriptException("No parameter specified!");
        }

        if (state.getProof().openEnabledGoals().size() != args.goals.intValue()) {
            throw new ScriptException(
                "Assertion failed: number of open goals is " +
                    state.getProof().openGoals().size() +
                    ", but should be " +
                    args.goals.intValue());
        }
    }

    @Override
    public String getName() {
        return "breakpoint";
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
