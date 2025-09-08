package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.scripts.meta.Option;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import java.util.ArrayList;
import java.util.Deque;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import java.util.Stack;

public class BranchesCommand extends AbstractCommand {
    public BranchesCommand() {
        super(Parameters.class);
    }

    @Override
    public void execute(ScriptCommandAst arguments) throws ScriptException, InterruptedException {
        var args = state().getValueInjector().inject(new BranchesCommand.Parameters(), arguments);

        Stack<Integer> stack = (Stack<Integer>) state.getUserData("_branchStack");
        if (stack == null) {
            stack = new Stack<>();
            state.putUserData("_branchStack", stack);
        }

        switch (args.mode) {
        case "push":
            Node node = state.getFirstOpenAutomaticGoal().node();
            // this is the first goal. The parent is the decision point
            node = node.parent();
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
        default:
            throw new ScriptException();
        }
    }

    private Goal findGoalByName(Node root, String branch) throws ScriptException {
        Iterator<Node> it = root.childrenIterator();
        List<String> knownBranchLabels = new ArrayList<>();
        while (it.hasNext()) {
            Node node = it.next();
            String label = node.getNodeInfo().getBranchLabel();
            knownBranchLabels.add(label);
            if (branch.equals(label)) {
                return findGoalByNode(root.proof(), node);
            }
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

    @Override
    public String getName() {
        return "branches";
    }

    public static class Parameters {
        /** A formula defining the goal to select */
        @Option(value = "#2")
        public String mode;
        @Option(value = "branch")
        public String branch;
        @Option(value = "child")
        public int child;
    }

}
