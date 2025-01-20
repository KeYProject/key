/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;

public class AllCommand extends AbstractCommand<Map<String, Object>> {

    public AllCommand() {
        super(null);
    }

    @Override
    public Map<String, Object> evaluateArguments(EngineState state, Map<String, Object> arguments) {
        return arguments;
    }

    @Override
    public String getName() {
        return "onAll";
    }

    @Override
    protected void execute(Map<String, Object> args) throws ScriptException, InterruptedException {
        String wrappedCmdname = args.get("#2").toString();
        if (wrappedCmdname == null) {
            throw new ScriptException("Missing command to apply onAll to");
        }

        ProofScriptCommand<?> command = ProofScriptEngine.getCommand(wrappedCmdname);
        if (command == null) {
            throw new ScriptException("Unknown command: " + wrappedCmdname);
        }

        var newArgs = rearrangeArgs(args);

        try {
            executeWrappedCommand(command, newArgs);
        } catch (Exception e) {
            throw new ScriptException(e);
        }

    }

    private HashMap<String, Object> rearrangeArgs(Map<String, Object> args) {
        HashMap<String, Object> newArgs = new HashMap<>();
        for (Entry<String, Object> en : args.entrySet()) {
            if (en.getKey().matches("#[0-9]+")) {
                int no = Integer.parseInt(en.getKey().substring(1));
                if (no != 1) {
                    newArgs.put("#" + (no - 1), en.getValue());
                }
            } else {
                newArgs.put(en.getKey(), en.getValue());
            }
        }
        return newArgs;
    }

    private <A> void executeWrappedCommand(ProofScriptCommand<A> command,
                                           Map<String, Object> newArgs) throws Exception {
        A params = command.evaluateArguments(state, newArgs);

        // Node selectedNode = state.getSelectedNode();
        for (Goal g : proof.openGoals()) {
            // if (isBelow(g, selectedNode)) {
            state.setGoal(g);
            command.execute(uiControl, params, state);
            // }
        }
        // state.setGoal(selectedNode);
    }

    private boolean isBelow(Goal g, Node above) {
        if (above == null) {
            return true;
        }

        Node node = g.node();
        while (node != null) {
            if (node == above) {
                return true;
            }
            node = node.parent();
        }

        return false;
    }
}
