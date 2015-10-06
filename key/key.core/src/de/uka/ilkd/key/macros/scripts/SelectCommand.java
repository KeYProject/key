package de.uka.ilkd.key.macros.scripts;

import java.util.Deque;
import java.util.LinkedList;
import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

public class SelectCommand extends AbstractCommand {

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Proof proof,
            Map<String, String> args, Map<String, Object> stateMap)
            throws ScriptException, InterruptedException {

        String formulaString = args.get("formula");
        if(formulaString == null) {
            throw new ScriptException("Missing 'formula' argument for select");
        }

        try {
            Term t = toTerm(proof, stateMap, formulaString, Sort.FORMULA);

            Goal g = findGoalWith(t, proof);

            stateMap.put(GOAL_KEY, g);

        } catch (ParserException e) {
            throw new ScriptException("illegal formula: " + formulaString, e);
        }

    }

    private Goal findGoalWith(Term formula, Proof proof) throws ScriptException {

        Goal g;
        Deque<Node> choices = new LinkedList<Node>();
        Node node = proof.root();
        while(node != null) {
            assert !node.isClosed();
            int childCount = node.childrenCount();

            Sequent seq;
            switch (childCount) {
            case 0:
                seq = node.sequent();
                if(contains(seq, formula)) {
                    g = getGoal(proof.openGoals(), node);
                    if(g.isAutomatic()) {
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
                    if(!child.isClosed()) {
                        if(next == null) {
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
        return contains(seq.antecedent(), formula) || contains(seq.succedent(), formula);
    }

    private boolean contains(Semisequent semiseq, Term formula) {
        for(SequentFormula sf : semiseq.asList()) {
            if(sf.formula().equalsModRenaming(formula)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public String getName() {
        return "select";
    }

}
