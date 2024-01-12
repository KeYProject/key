/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import de.uka.ilkd.key.macros.TryCloseMacro;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.macros.scripts.meta.ValueInjector;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;

import org.key_project.util.collection.ImmutableList;

/**
 * The script command tryclose" has two optional arguments:
 * <ul>
 * <li>steps: INTEGER number of steps to use</li>
 * <li>#2: STRING the number of the branch which should be closed</li>
 * </ul>
 *
 * If #2 is not given or not a number, the TryClose macro is applied to all open goals.
 */
public class TryCloseCommand extends AbstractCommand<TryCloseCommand.TryCloseArguments> {
    public TryCloseCommand() {
        super(TryCloseArguments.class);
    }

    @Override
    public TryCloseArguments evaluateArguments(EngineState state, Map<String, String> arguments)
            throws Exception {
        return ValueInjector.injection(this, new TryCloseArguments(), arguments);
    }

    @Override
    public void execute(TryCloseArguments args) throws ScriptException, InterruptedException {

        TryCloseMacro macro =
            args.steps == null ? new TryCloseMacro() : new TryCloseMacro(args.steps);

        boolean branch = "branch".equals(args.branch);
        Node target;
        if (branch) {
            target = state.getFirstOpenAutomaticGoal().node();
        } else {
            try {
                int num = Integer.parseInt(args.branch);
                ImmutableList<Goal> goals = state.getProof().openEnabledGoals();
                if (num >= 0) {
                    target = goals.take(num).head().node();
                } else {
                    target = goals.take(goals.size() + num).head().node();
                }
            } catch (NumberFormatException e) {
                target = state.getProof().root();
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
        @Option(value = "steps", required = false)
        public Integer steps;
        @Option(value = "#2", required = false)
        public String branch;
        @Option(value = "assertClosed", required = false)
        public Boolean assertClosed = false;
    }
}
