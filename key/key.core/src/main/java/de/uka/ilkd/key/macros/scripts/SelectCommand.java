package de.uka.ilkd.key.macros.scripts;

import java.util.Deque;
import java.util.LinkedList;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;

import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.util.parsing.BuildingException;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

public class SelectCommand extends AbstractCommand<SelectCommand.Parameters> {
    public SelectCommand() {
        super(Parameters.class);
    }

    @Override
    public Parameters evaluateArguments(EngineState state,
            Map<String, String> arguments) throws Exception {
        // Check formula syntax here, only BuildingExceptions are allowed
        var formula = arguments.get("formula");
        if (formula != null) {
            try {
                state.toTerm(formula, null);
            } catch(BuildingException e) {
                // Ignored
            }
        }

        return state.getValueInjector().inject(this, new Parameters(),
                arguments);
    }

    @Override
    public void execute(Parameters args)
            throws ScriptException, InterruptedException {
        Goal g;
        if (args.number != null && args.formula == null
                && args.branch == null) {
            ImmutableList<Goal> goals = state.getProof().openEnabledGoals();

            if (args.number >= 0) {
                g = goals.take(args.number).head();
            } else {
                g = goals.take(goals.size() + args.number).head();
            }
        } else if (args.formula != null && args.number == null
                && args.branch == null) {
            g = findGoalWithFormula(args.formula, state.getProof());
        } else if (args.branch != null && args.formula == null
                && args.number == null) {
            g = findGoalWith(args.branch, state.getProof());
        } else {
            throw new ScriptException(
                    "Exactly one of 'formula', 'branch' or 'number' are required");
        }

        state.setGoal(g);
    }

    private Goal findGoalWith(String branchTitle, Proof proof)
            throws ScriptException {
        return findGoalWith(
                node -> Optional.ofNullable(node.getNodeInfo().getBranchLabel())
                        .orElse("").equals(branchTitle),
                node -> getFirstSubtreeGoal(node, proof), proof);
    }

    private static Goal getFirstSubtreeGoal(Node node, Proof proof) {
        Goal goal;
        if (node.leaf() && //
                (goal = EngineState.getGoal(proof.openGoals(), node)) != null) {
            return goal;
        }

        if (node.childrenCount() == 0) {
            return null;
        }

        final Iterable<Node> children = (() -> node.childrenIterator());
        for (Node child : children) {
            goal = getFirstSubtreeGoal(child, proof);
            if (goal != null) {
                return goal;
            }
        }

        return null;
    }

    private boolean findFormulaInLeaf(String formula, Node node) {
        // We have to set the goal since it changes the variables that exist
        // And the formula can only be valid if they do exist
        state.setGoal(node);
        try {
            var term = state.toTerm(formula, null);
            return contains(node.sequent(), term);
        } catch(BuildingException e) {
            return false;
        } catch(ParserException | ScriptException e) {
            // Should not happen, let's print it anyways
            new Exception("Syntax was checked earlier and should be valid here", e).printStackTrace();
            return false;
        }
    }

    private Goal findGoalWithFormula(String formula, Proof proof)
            throws ScriptException {
        return findGoalWith(
                node -> node.leaf() && findFormulaInLeaf(formula, node),
                node -> EngineState.getGoal(proof.openGoals(), node), proof);
    }

    private Goal findGoalWith(Function<Node, Boolean> filter,
            Function<Node, Goal> goalRetriever, Proof proof)
            throws ScriptException {
        Deque<Node> choices = new LinkedList<Node>();
        Node node = proof.root();

        while (node != null) {
            assert !node.isClosed();
            int childCount = node.childrenCount();

            if (filter.apply(node)) {
                final Goal g = goalRetriever.apply(node);
                if (g.isAutomatic()) {
                    return g;
                }
            }

            switch (childCount) {
            case 0:
                node = choices.pollLast();
                break;

            case 1:
                node = node.child(0);
                break;

            default:
                Node next = null;
                for (int i = 0; i < childCount; i++) {
                    Node child = node.child(i);
                    if (!child.isClosed()) {
                        if (next == null) {
                            next = child;
                        } else {
                            choices.add(child);
                        }
                    }
                }
                assert next != null;
                node = next;
                break;
            }
        }

        throw new ScriptException("There is no such goal");
    }

    private boolean contains(Sequent seq, Term formula) {
        return contains(seq.antecedent(), formula)
                || contains(seq.succedent(), formula);
    }

    private boolean contains(Semisequent semiseq, Term formula) {
        for (SequentFormula sf : semiseq.asList()) {
            if (sf.formula().equalsModRenaming(formula)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public String getName() {
        return "select";
    }

    public class Parameters {
        /** A formula defining the goal to select */
        @Option(value = "formula", required = false)
        public String formula;
        /**
         * The number of the goal to select, starts with 0.
         * Negative indices are also allowed: -1 is the last goal, -2 the second-to-last, etc.
         */
        @Option(value = "number", required = false)
        public Integer number;
        /** The name of the branch to select */
        @Option(value = "branch", required = false)
        public String branch;
    }

}
