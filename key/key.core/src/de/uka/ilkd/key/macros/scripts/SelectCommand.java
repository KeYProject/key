package de.uka.ilkd.key.macros.scripts;

import java.util.Deque;
import java.util.LinkedList;
import java.util.Map;

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

    @Override public Parameters evaluateArguments(EngineState state,
            Map<String, String> arguments) throws Exception {
        return state.getValueInjector().inject(this, new Parameters(), arguments);
    }

    @Override public void execute(Parameters args)
            throws ScriptException, InterruptedException {
        Goal g;
        if (args.number != null && args.formula == null) {
            g = state.getProof().openEnabledGoals().take(args.number).head();
        } else if (args.formula != null && args.number == null) {
            g = findGoalWith(args.formula, state.getProof());
        } else {
            throw new ScriptException("Exactly one of 'formula' or 'number' are required");
        }

        state.setGoal(g);
    }

    private Goal findGoalWith(Term formula, Proof proof)
            throws ScriptException {

        Goal g;
        Deque<Node> choices = new LinkedList<Node>();
        Node node = proof.root();
        while (node != null) {
            assert !node.isClosed();
            int childCount = node.childrenCount();

            Sequent seq;
            switch (childCount) {
            case 0:
                seq = node.sequent();
                if (contains(seq, formula)) {
                    g = EngineState.getGoal(proof.openGoals(), node);
                    if (g.isAutomatic()) {
                        return g;
                    }
                }
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
                        }
                        else {
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
        return contains(seq.antecedent(), formula) || contains(seq.succedent(),
                formula);
    }

    private boolean contains(Semisequent semiseq, Term formula) {
        for (SequentFormula sf : semiseq.asList()) {
            if (sf.formula().equalsModRenaming(formula)) {
                return true;
            }
        }
        return false;
    }

    @Override public String getName() {
        return "select";
    }

    public class Parameters {
        /** A formula defining the goal to select */
        @Option(value = "formula", required = false)
        public Term formula;
        /** The number of the goal to select, starts with 0 */
        @Option(value = "number", required = false)
        public Integer number;
    }

}
