/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.macros.TryCloseMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.scripts.meta.Argument;
import de.uka.ilkd.key.scripts.meta.Documentation;
import de.uka.ilkd.key.scripts.meta.Flag;
import de.uka.ilkd.key.scripts.meta.Option;

import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

/**
 * The script command tryclose" has two optional arguments:
 * <ul>
 * <li>steps: INTEGER number of steps to use</li>
 * <li>#2: STRING the number of the branch which should be closed</li>
 * </ul>
 *
 * If #2 is not given or not a number, the TryClose macro is applied to all open goals.
 */
@Documentation(category = "Control", value = """
        The `tryclose` command attempts to automatically close proof goals using the TryClose macro.
        It applies automatic proof strategies to discharge open goals.

        The command can target specific branches by number or name, or apply to all open goals.
        With the `assertClosed` flag, it will fail the script if closure is not achieved.

        #### Usage Examples
        - `tryclose` - Applies TryClose to all open goals
        - `tryclose 5` - Tries to close the 5th goal
        - `tryclose branch` - Applies TryClose to the current branch only
        - `tryclose assertClosed` - Fails if the goal cannot be closed
        """)
public class TryCloseCommand extends AbstractCommand {
    public TryCloseCommand() {
        super(TryCloseArguments.class);
    }

    @Override
    public void execute(ScriptCommandAst params) throws ScriptException, InterruptedException {
        var args = state().getValueInjector().inject(new TryCloseArguments(), params);

        TryCloseMacro macro =
            args.steps == null ? new TryCloseMacro() : new TryCloseMacro(args.steps);

        boolean branch = "branch".equals(args.branch);
        Node target;
        if (branch) {
            target = state().getFirstOpenAutomaticGoal().node();
        } else {
            try {
                int num = Integer.parseInt(args.branch);
                ImmutableList<Goal> goals = state().getProof().openEnabledGoals();
                if (num >= 0) {
                    target = goals.get(num).node();
                } else {
                    target = goals.get(goals.size() + num).node();
                }
            } catch (NumberFormatException e) {
                target = state().getProof().root();
            }
        }

        try {
            macro.applyTo(uiControl, target, null, uiControl);
            if (args.assertClosed && !target.isClosed()) {
                throw new ScriptException("Could not close subtree of node " + target.serialNr());
            }
        } catch (Exception e) {
            throw new ScriptException("tryclose caused an exception: " + e.getMessage(), e);
        }

    }

    @Override
    public String getName() {
        return "tryclose";
    }

    public static class TryCloseArguments {
        @Option(value = "steps")
        @Documentation("The maximum number of proof steps to perform")
        public @Nullable Integer steps;

        @Argument
        @Documentation("The branch identifier: a number (goal index), 'branch' (current branch), or omitted (all goals)")
        public @Nullable String branch;

        @Flag(value = "assertClosed")
        @Documentation("Fail the script if the target goal cannot be closed")
        public Boolean assertClosed = false;
    }
}
