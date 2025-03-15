/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.util.List;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.scripts.meta.ProofScriptArgument;

public class AllCommand implements ProofScriptCommand {
    private String documentation;

    @Override
    public List<ProofScriptArgument> getArguments() {
        return List.of();
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, ScriptCommandAst args,
            EngineState stateMap) throws ScriptException, InterruptedException {
        var block = args.commands();

        if (block == null) {
            throw new ScriptException("Missing command to apply onAll to");
        }

        var proof = stateMap.getProof();
        // Node selectedNode = state.getSelectedNode();
        for (Goal g : proof.openGoals()) {
            // if (isBelow(g, selectedNode)) {
            stateMap.setGoal(g);
            stateMap.getEngine().execute(uiControl, block);
            // }
        }
        // state.setGoal(selectedNode);
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
