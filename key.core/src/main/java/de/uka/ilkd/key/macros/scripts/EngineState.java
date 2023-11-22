/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.io.File;
import java.util.Deque;
import java.util.LinkedList;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Consumer;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.macros.scripts.meta.ValueInjector;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofSettings;

import org.key_project.util.collection.ImmutableList;

import org.antlr.v4.runtime.CharStreams;
import org.jspecify.annotations.NonNull;

/**
 * @author Alexander Weigl
 * @version 1 (28.03.17)
 */
public class EngineState {
    private final Proof proof;
    private final AbbrevMap abbrevMap = new AbbrevMap();
    /**
     * nullable
     */
    private Consumer<ProofScriptEngine.Message> observer;
    private File baseFileName = new File(".");
    private final ValueInjector valueInjector = ValueInjector.createDefault();
    private Goal goal;
    private Node lastSetGoalNode;

    /**
     * If set to true, outputs all commands to observers and console. Otherwise, only shows explicit
     * echo messages.
     */
    private boolean echoOn = true;

    /**
     * If set to true, an already closed proof leads to an exception if another goal should be
     * picked. Otherwise, script execution terminates without an exception.
     */
    private boolean failOnClosedOn = true;

    public EngineState(Proof proof) {
        this.proof = proof;
        valueInjector.addConverter(Term.class, (String s) -> toTerm(s, null));
        valueInjector.addConverter(Sequent.class, this::toSequent);
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
     * Returns the first open goal, which has to be automatic iff checkAutomatic is true.
     *
     * @param checkAutomatic Set to true if the returned {@link Goal} should be automatic.
     * @return the first open goal, which has to be automatic iff checkAutomatic is true.
     *
     * @throws ProofAlreadyClosedException If the proof is already closed when calling this method.
     * @throws ScriptException If there is no such {@link Goal}, or something else goes wrong.
     */
    @SuppressWarnings("unused")
    public @NonNull Goal getFirstOpenGoal(boolean checkAutomatic) throws ScriptException {
        if (proof.closed()) {
            throw new ProofAlreadyClosedException("The proof is closed already");
        }

        Node rootNodeForSearch = proof.root();
        Goal newGoal = goal;
        if (newGoal != null
                && ((checkAutomatic && !newGoal.isAutomatic()) || newGoal.node().isClosed())) {
            assert rootNodeForSearch != null;
            /*
             * The first subtree of the previous goal is closed. Try with other subtrees.
             */
            rootNodeForSearch = goUpUntilOpen(lastSetGoalNode);
            newGoal = null;
        }

        if (newGoal != null) {
            return newGoal;
        }

        newGoal = findGoalFromRoot(rootNodeForSearch, checkAutomatic);
        if (newGoal == null) {
            throw new ScriptException("There must be an open goal at this point");
        }

        lastSetGoalNode = newGoal.node();

        return newGoal;
    }

    /**
     * @return The first open and automatic {@link Goal}.
     *
     * @throws ScriptException If there is no such {@link Goal}.
     */
    public Goal getFirstOpenAutomaticGoal() throws ScriptException {
        return getFirstOpenGoal(true);
    }

    private static Node goUpUntilOpen(final Node start) {
        Node currNode = start;

        while (currNode.isClosed()) {
            /*
             * There should always be a non-closed parent since we check whether the proof is closed
             * at the beginning.
             */
            currNode = currNode.parent();
        }

        return currNode;
    }

    private Goal findGoalFromRoot(final Node rootNode, boolean checkAutomatic) {
        final Deque<Node> choices = new LinkedList<>();

        Goal result = null;
        Node node = rootNode;

        loop: while (node != null) {
            if (node.isClosed()) {
                return null;
            }

            int childCount = node.childrenCount();

            switch (childCount) {
            case 0 -> {
                result = getGoal(proof.openGoals(), node);
                if (!checkAutomatic || Objects.requireNonNull(result).isAutomatic()) {
                    // We found our goal
                    break loop;
                }
                node = choices.pollLast();
            }
            case 1 -> node = node.child(0);
            default -> {
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
            }
            }
        }

        return result;
    }


    public Term toTerm(String string, Sort sort) throws ParserException, ScriptException {
        final var io = getKeyIO();
        var term = io.parseExpression(string);
        if (sort == null || term.sort().equals(sort))
            return term;
        else
            throw new IllegalStateException(
                "Unexpected sort for term: " + term + ". Expected: " + sort);
    }

    @NonNull
    private KeyIO getKeyIO() throws ScriptException {
        Services services = proof.getServices();
        KeyIO io = new KeyIO(services, getFirstOpenAutomaticGoal().getLocalNamespaces());
        io.setAbbrevMap(abbrevMap);
        return io;
    }

    public Sort toSort(String sortName) throws ScriptException {
        return (getFirstOpenAutomaticGoal() == null ? getProof().getServices().getNamespaces()
                : getFirstOpenAutomaticGoal().getLocalNamespaces()).sorts().lookup(sortName);
    }

    public Sequent toSequent(String sequent) throws ScriptException {
        return getKeyIO().parseSequent(CharStreams.fromString(sequent));
    }

    public int getMaxAutomaticSteps() {
        if (proof != null) {
            return proof.getSettings().getStrategySettings().getMaxSteps();
        } else {
            return ProofSettings.DEFAULT_SETTINGS.getStrategySettings().getMaxSteps();
        }
    }

    public void setMaxAutomaticSteps(int steps) {
        if (proof != null) {
            proof.getSettings().getStrategySettings().setMaxSteps(steps);
        }
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(steps);
    }

    public Consumer<ProofScriptEngine.Message> getObserver() {
        return observer;
    }

    public void setObserver(Consumer<ProofScriptEngine.Message> observer) {
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

    public boolean isFailOnClosedOn() {
        return failOnClosedOn;
    }

    public void setFailOnClosedOn(boolean failOnClosedOn) {
        this.failOnClosedOn = failOnClosedOn;
    }
}
