/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.util.List;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.scripts.meta.ProofScriptArgument;

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

    /**
     * {@inheritDoc}
     */
    @Override
    public String getDocumentation() {
        return """
                Applies the given command to all the open goals.""";
    }
}
