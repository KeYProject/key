/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.util.List;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.scripts.meta.Documentation;
import de.uka.ilkd.key.scripts.meta.ProofScriptArgument;

@Documentation(category = "Control", value = """
        Executes a given block of script commands on all open goals.
        The current goal is set to each open goal in turn while executing the block.
        It expects exactly one positional argument, which is the block to be executed on each goal.
        
        #### Examples:
        * `onAll { smt solver="z3"; }`
        * `onAll { auto; }`
        """)
public class AllCommand implements ProofScriptCommand {
    @Override
    public List<ProofScriptArgument> getArguments() {
        return List.of();
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, ScriptCommandAst args,
            EngineState stateMap) throws ScriptException, InterruptedException {
        if (args.positionalArgs().size() != 1) {
            throw new ScriptException(
                "Invalid number of positional arguments to 'onAll'. Pos. arguments: "
                    + args.positionalArgs().size());
        }

        var block = stateMap.getValueInjector().convert(
            args.positionalArgs().getFirst(),
            ScriptBlock.class);

        var proof = stateMap.getProof();
        for (Goal g : proof.openGoals()) {
            stateMap.setGoal(g);
            stateMap.getEngine().execute(uiControl, block);
        }
    }


    @Override
    public String getName() {
        return "onAll";
    }
}
