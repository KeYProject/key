package de.uka.ilkd.key.macros.scripts;

import java.io.File;
import java.io.StringReader;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Observer;
import java.util.Optional;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.macros.scripts.meta.ValueInjector;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofSettings;

/**
 * @author Alexander Weigl
 * @version 1 (28.03.17)
 */
public class EngineState {
    private final static DefaultTermParser PARSER = new DefaultTermParser();
    private final Map<String, Object> arbitraryVariables = new HashMap<>();
    private final Proof proof;
    private AbbrevMap abbrevMap = new AbbrevMap();
    /**
     * nullable
     */
    private Observer observer;
    private File baseFileName = new File(".");
    private ValueInjector valueInjector = ValueInjector.createDefault();
    private Goal goal;
    private Node lastSetGoalNode;

    /**
     * If set to true, outputs all commands to observers and console. Otherwise,
     * only shows explicit echo messages.
     */
    private boolean echoOn = true;

    public EngineState(Proof proof) {
        this.proof = proof;
        valueInjector.addConverter(Term.class, (String s) -> toTerm(s, null));
        valueInjector.addConverter(Sort.class, this::toSort);
    }

    protected static Goal getGoal(ImmutableList<Goal> openGoals, Node node) {
        for (Goal goal : openGoals) {
            if (goal.node() == node) {
                return goal;
            }
        }
        return null;
    }

    public void setGoal(Goal g) {
        goal = g;
        lastSetGoalNode = Optional.ofNullable(g).map(Goal::node).orElse(null);
    }

    public Proof getProof() {
        return proof;
    }

    /**
     * Returns the first open goal, which has to be automatic iff checkAutomatic
     * is true.
     *
     * @param checkAutomatic
     *            Set to true if the returned {@link Goal} should be automatic.
     * @return the first open goal, which has to be automatic iff checkAutomatic
     *         is true.
     *
     * @throws ScriptException
     *             If there is no such {@link Goal}, or something else goes
     *             wrong.
     */
    @SuppressWarnings("unused")
    public Goal getFirstOpenGoal(boolean checkAutomatic)
            throws ScriptException {
        if (proof.closed()) {
            throw new ScriptException("The proof is closed already");
        }

        Node rootNodeForSearch = proof.root();
        Goal newGoal = goal;
        if (newGoal != null && ((checkAutomatic && !newGoal.isAutomatic())
                || newGoal.node().isClosed())) {
            assert rootNodeForSearch != null;
            /*
             * The first subtree of the previous goal is closed. Try with other
             * subtrees.
             */
            rootNodeForSearch = goUpUntilOpen(lastSetGoalNode);
            newGoal = null;
        }

        if (newGoal != null) {
            return newGoal;
        }

        newGoal = findGoalFromRoot(rootNodeForSearch, checkAutomatic);
        lastSetGoalNode = newGoal.node();

        if (newGoal == null) {
            throw new ScriptException(
                    "There must be an open goal at this point");
        }

        return newGoal;
    }

    /**
     * @return The first open and automatic {@link Goal}.
     *
     * @throws ScriptException
     *             If there is no such {@link Goal}.
     */
    public Goal getFirstOpenAutomaticGoal() throws ScriptException {
        return getFirstOpenGoal(true);
    }

    private static Node goUpUntilOpen(final Node start) {
        Node currNode = start;

        while (currNode.isClosed()) {
            /*
             * There should always be a non-closed parent since we check whether
             * the proof is closed at the beginning.
             */
            currNode = currNode.parent();
        }

        return currNode;
    }

    private Goal findGoalFromRoot(final Node rootNode, boolean checkAutomatic) {
        final Deque<Node> choices = new LinkedList<Node>();

        Goal result = null;
        Node node = rootNode;

        loop: while (node != null) {
            if (node.isClosed()) {
                return null;
            }

            int childCount = node.childrenCount();

            switch (childCount) {
            case 0:
                result = getGoal(proof.openGoals(), node);
                if (!checkAutomatic || result.isAutomatic()) {
                    // We found our goal
                    break loop;
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

        return result;
    }

    public Term toTerm(String string, Sort sort)
            throws ParserException, ScriptException {
        StringReader reader = new StringReader(string);
        Services services = proof.getServices();
        Term formula = PARSER.parse(reader, sort, services,
                getFirstOpenAutomaticGoal().getLocalNamespaces(), abbrevMap);
        return formula;
    }

    public Sort toSort(String sortName)
            throws ParserException, ScriptException {
        return (getFirstOpenAutomaticGoal() == null
                ? getProof().getServices().getNamespaces()
                : getFirstOpenAutomaticGoal().getLocalNamespaces()).sorts()
                        .lookup(sortName);
    }

    public Sequent toSequent(String sequent)
            throws ParserException, ScriptException {
        StringReader reader = new StringReader(sequent);
        Services services = proof.getServices();

        Sequent seq = PARSER.parseSeq(reader, services,
                getFirstOpenAutomaticGoal().getLocalNamespaces(),
                getAbbreviations());
        return seq;
    }

    public int getMaxAutomaticSteps() {
        if (proof != null) {
            return proof.getSettings().getStrategySettings().getMaxSteps();
        } else {
            return ProofSettings.DEFAULT_SETTINGS.getStrategySettings()
                    .getMaxSteps();
        }
    }

    public void setMaxAutomaticSteps(int steps) {
        if (proof != null) {
            proof.getSettings().getStrategySettings().setMaxSteps(steps);
        }
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(steps);
    }

    public Observer getObserver() {
        return observer;
    }

    public void setObserver(Observer observer) {
        this.observer = observer;
    }

    public File getBaseFileName() {
        return baseFileName;
    }

    public void setBaseFileName(File baseFileName) {
        this.baseFileName = baseFileName;
    }

    public ValueInjector getValueInjector() {
        return valueInjector;
    }

    public AbbrevMap getAbbreviations() {
        return abbrevMap;
    }

    public void setGoal(Node node) {
        setGoal(getGoal(proof.openGoals(), node));
    }

    public boolean isEchoOn() {
        return echoOn;
    }

    public void setEchoOn(boolean echoOn) {
        this.echoOn = echoOn;
    }

}
