package de.uka.ilkd.key.macros.scripts;

import java.io.StringReader;
import java.util.Deque;
import java.util.LinkedList;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofSettings;

public abstract class AbstractCommand implements ProofScriptCommand {

    private static DefaultTermParser PARSER = new DefaultTermParser();
    private static AbbrevMap EMPTY_MAP = new AbbrevMap();

    final protected Goal getFirstOpenGoal(Proof proof) throws ScriptException {

        Node node = proof.root();

        if(node.isClosed()) {
            throw new ScriptException("The proof is closed already");
        }

        Goal g;
        Deque<Node> choices = new LinkedList<Node>();

        while(node != null) {
            assert !node.isClosed();
            int childCount = node.childrenCount();

            switch (childCount) {
            case 0:
                g = getGoal(proof.openGoals(), node);
                if(g.isAutomatic()) {
                    return g;
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
        assert false : "There must be an open goal at this point";
        return null;
    }

    final protected static Term toTerm(Proof proof, String string, Sort sort) throws ParserException {
        StringReader reader = new StringReader(string);
        Services services = proof.getServices();
        Term formula = PARSER.parse(reader, sort, services, services.getNamespaces(), EMPTY_MAP);
        return formula;
    }

    private static Goal getGoal(ImmutableList<Goal> openGoals, Node node) {
        for (Goal goal : openGoals) {
            if(goal.node() == node) {
                return goal;
            }
        }
        throw new Error("unreachable");
    }

    final protected static int getMaxAutomaticSteps(Proof proof) {
        if (proof != null) {
            return proof.getSettings().getStrategySettings().getMaxSteps();
        } else {
            return ProofSettings.DEFAULT_SETTINGS.getStrategySettings().getMaxSteps();
        }
    }

    public void setMaxAutomaticSteps(Proof proof, int steps) {
        if (proof != null) {
            proof.getSettings().getStrategySettings().setMaxSteps(steps);
        }
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(steps);
     }

}
