package de.uka.ilkd.key.macros.scripts;

import java.io.StringReader;
import java.util.Deque;
import java.util.LinkedList;
import java.util.Map;

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

    public static final String GOAL_KEY = "goal";
    public static final String ABBREV_KEY = "abbrMap";
    private static DefaultTermParser PARSER = new DefaultTermParser();
    private static AbbrevMap EMPTY_MAP = new AbbrevMap();

    protected static Goal getFirstOpenGoal(Proof proof, Map<String, Object> state) throws ScriptException {

        Object fixedGoal = state.get(GOAL_KEY);
        if(fixedGoal instanceof Node) {
            Goal g = getGoal(proof.openGoals(), (Node)fixedGoal);
            if(g != null) {
                return g;
            }
        }

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

    final protected static Term toTerm(Proof proof, Map<String, Object> state, String string, Sort sort) throws ParserException, ScriptException {

        AbbrevMap abbrMap = (AbbrevMap)state.get(ABBREV_KEY);
        if(abbrMap == null) {
            abbrMap = EMPTY_MAP;
        }

        StringReader reader = new StringReader(string);
        Services services = proof.getServices();
        Term formula = PARSER.parse(reader, sort, services, services.getNamespaces(), abbrMap);
        return formula;
    }

    final protected static Sort toSort(Proof proof, Map<String, Object> state, String string) throws ParserException, ScriptException {
        StringReader reader = new StringReader(string);
        Services services = proof.getServices();
        Sort sort = (Sort) services.getNamespaces().sorts().lookup(string);
        return sort;
    }

    final protected static Goal getGoal(ImmutableList<Goal> openGoals, Node node) {
        for (Goal goal : openGoals) {
            if(goal.node() == node) {
                return goal;
            }
        }
        return null;
    }

    final protected static int getMaxAutomaticSteps(Proof proof) {
        if (proof != null) {
            return proof.getSettings().getStrategySettings().getMaxSteps();
        } else {
            return ProofSettings.DEFAULT_SETTINGS.getStrategySettings().getMaxSteps();
        }
    }

    final protected void setMaxAutomaticSteps(Proof proof, int steps) {
        if (proof != null) {
            proof.getSettings().getStrategySettings().setMaxSteps(steps);
        }
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(steps);
     }

}
