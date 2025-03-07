/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import de.uka.ilkd.key.macros.scripts.meta.Documentation;
import de.uka.ilkd.key.macros.scripts.meta.Option;

/**
 * Halts the script if some condition is not met.
 *
 * See exported documentation at {@link Parameters} at the end of this file.
 *
 * @author lanzinger
 */
public class AssertCommand extends AbstractCommand<AssertCommand.Parameters> {

    /**
     * Instantiates a new assert command.
     */
    public AssertCommand() {
        super(Parameters.class);
    }

    @Override
    public Parameters evaluateArguments(EngineState state,
            Map<String, Object> arguments)
            throws Exception {
        return state.getValueInjector().inject(this, new Parameters(), arguments);
    }

    @Override
    public void execute(Parameters args) throws ScriptException, InterruptedException {
        if (args.goals == null) {
            throw new ScriptException("No parameter specified!");
        }

        if (state.getProof().openEnabledGoals().size() != args.goals) {
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
    @Documentation("""
            The assert command checks if the number of open and enabled goals is equal to the given number.
            If not, the script is halted with an error message.
            
            Deprecated: This command is deprecated and should not be used in new scripts.
            The name of this command is likely to change since "assert" will
            be used for a more general purpose. You may find that this is called
            "failUnless".
            """)
    public static class Parameters {
        @Option(value="goals",
                help="The expected number of open and enabled goals.")
        public Integer goals;
    }
}
