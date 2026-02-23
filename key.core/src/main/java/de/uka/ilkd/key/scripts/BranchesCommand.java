/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.util.ArrayList;
import java.util.Deque;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import java.util.Stack;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.scripts.meta.Argument;
import de.uka.ilkd.key.scripts.meta.Option;

import org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

public class BranchesCommand extends AbstractCommand {

    public BranchesCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "branches";
    }

    @Override
    public void execute(ScriptCommandAst arguments) throws ScriptException, InterruptedException {
        var args = state().getValueInjector().inject(new BranchesCommand.Parameters(), arguments);

        Stack<Integer> stack = (Stack<Integer>) state.getUserData("_branchStack");
        if (stack == null) {
            stack = new Stack<>();
            state.putUserData("_branchStack", stack);
        }

        if (args.mode == null) {
            throw new ScriptException("For 'branches', a mode must be specified");
        }

        switch (args.mode) {
            case "push":
                ensureSingleGoal();
                Node node = state.getFirstOpenAutomaticGoal().node();
                // this is the first goal. The parent is the decision point
                stack.push(node.serialNr());
                break;
            case "pop":
                stack.pop();
                break;
            case "select":
                Node root = findNodeByNumber(proof, stack.peek());
                Goal goal;
                if (args.branch == null) {
                    goal = findGoalByNode(state.getProof(), root.child(args.child));
                } else {
                    goal = findGoalByName(root, args.branch);
                }
                state.setGoal(goal);
                break;
            case "single":
                root = findNodeByNumber(proof, stack.peek());
                TacletApp ta = (TacletApp) root.getAppliedRuleApp();
                ImmutableList<TacletGoalTemplate> templates = ta.taclet().goalTemplates();

                int no = 0;
                int found = -1;
                for (TacletGoalTemplate template : templates) {
                    if (!"main".equals(template.tag())) {
                        if (found != -1) {
                            throw new ScriptException("More than one non-main goal found");
                        }
                        found = no;
                    }
                    no++;
                }
                if (found == -1) {
                    throw new ScriptException("No single non-main goal found");
                }

                // For some reason, the child index is reversed between the node and the templates
                found = templates.size() - 1 - found;
                goal = findGoalByNode(proof, root.child(found));
                state.setGoal(goal);
                break;
            default:
                throw new ScriptException(
                    "Unknown mode " + args.mode + " for the 'branches' command");
        }
    }

    private void ensureSingleGoal() {
        // state.
    }

    private Goal findGoalByName(Node root, String branch) throws ScriptException {
        Iterator<Node> it = root.childrenIterator();
        List<String> knownBranchLabels = new ArrayList<>();
        int number = 1;
        while (it.hasNext()) {
            Node node = it.next();
            String label = node.getNodeInfo().getBranchLabel();
            if (label == null) {
                label = "Case " + number;
            }
            knownBranchLabels.add(label);
            if (branch.equals(label)) {
                return findGoalByNode(root.proof(), node);
            }
            number++;
        }
        throw new ScriptException(
            "Unknown branch " + branch + ". Known branches are " + knownBranchLabels);
    }

    private static Goal findGoalByNode(Proof proof, Node node) throws ScriptException {
        Optional<Goal> result =
            proof.openEnabledGoals().stream().filter(g -> g.node() == node).findAny();
        if (result.isEmpty()) {
            throw new ScriptException();
        }
        return result.get();
    }

    private Node findNodeByNumber(Proof proof, int serial) throws ScriptException {
        Deque<Node> todo = new LinkedList<>();
        todo.add(proof.root());
        while (!todo.isEmpty()) {
            Node n = todo.remove();
            if (n.serialNr() == serial) {
                return n;
            }
            Iterator<Node> it = n.childrenIterator();
            while (it.hasNext()) {
                todo.add(it.next());
            }
        }
        throw new ScriptException();
    }

    public static class Parameters {
        /** A formula defining the goal to select */
        @Argument
        public String mode;
        @Option(value = "branch")
        public @Nullable String branch;
        @Option(value = "child")
        public @Nullable Integer child;
    }

}
