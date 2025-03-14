/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.scripts.meta.ProofScriptArgument;

public class AllCommand implements ProofScriptCommand<Map<String, Object>> {
    private String documentation;

    @Override
    public List<ProofScriptArgument<Map<String, Object>>> getArguments() {
        return List.of();
    }

    @Override
    public Map<String, Object> evaluateArguments(EngineState state, Map<String, Object> arguments) {
        return arguments;
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Map<String, Object> args,
            EngineState stateMap) throws ScriptException, InterruptedException {
        var block = (KeYParser.ProofScriptContext) args.get(ProofScriptEngine.KEY_SUB_SCRIPT);

        if (block == null) {
            throw new ScriptException("Missing command to apply onAll to");
        }

        var proof = stateMap.getProof();
        // Node selectedNode = state.getSelectedNode();
        for (Goal g : proof.openGoals()) {
            // if (isBelow(g, selectedNode)) {
            stateMap.setGoal(g);
            stateMap.getEngine().execute(uiControl, block.proofScriptCommand());
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
