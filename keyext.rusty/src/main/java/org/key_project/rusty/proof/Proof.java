/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof;

import java.util.Iterator;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofObject;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.proof.calculus.RustySequentKit;
import org.key_project.rusty.proof.init.InitConfig;
import org.key_project.rusty.settings.ProofSettings;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;


public class Proof implements ProofObject<Goal>, Named {
    /**
     * name of the proof
     */
    private final Name name;

    /**
     * The time when the {@link Proof} instance was created.
     */
    final long creationTime = System.currentTimeMillis();

    /**
     * the root of the proof
     */
    private Node root;

    /**
     * list with the open goals of the proof
     */
    private ImmutableList<Goal> openGoals = ImmutableSLList.nil();

    /**
     * list with the closed goals of the proof, needed to make pruning in closed branches possible.
     * If the list needs too much memory, pruning can be disabled via the command line option
     * "--no-pruning-closed". In this case the list will not be filled.
     */
    private ImmutableList<Goal> closedGoals = ImmutableSLList.nil();

    /**
     * the logic configuration for this proof, i.e., logic signature, rules etc.
     */
    private InitConfig initConfig;

    /**
     * declarations &c, read from a problem file or otherwise
     */
    private String problemHeader = "";

    /**
     * constructs a new empty proof with name
     */
    private Proof(Name name, InitConfig initConfig) {
        this.name = name;
        assert initConfig != null : "Tried to create proof without valid services.";
        this.initConfig = initConfig;

        if (initConfig.getSettings() == null) {
            // if no settings have been assigned yet, take default settings
            initConfig.setSettings(new ProofSettings());
        }

        final Services services = this.initConfig.getServices();
        services.setProof(this);
    }

    /**
     * constructs a new empty proof with name
     */
    public Proof(String name, InitConfig initConfig) {
        this(new Name(name), initConfig);
    }

    private Proof(String name, org.key_project.prover.sequent.Sequent problem,
            TacletIndex tacletIndex,
            InitConfig initConfig) {
        this(new Name(name), initConfig);

        final var rootNode = new Node(this, problem);
        final var firstGoal =
            new Goal(rootNode, tacletIndex, initConfig.getServices());
        openGoals = openGoals.prepend(firstGoal);
        setRoot(rootNode);
    }

    public Proof(String name, Term problem, InitConfig initConfig) {
        this(name,
            RustySequentKit
                    .createSuccSequent(ImmutableSLList.singleton(new SequentFormula(problem))),
            initConfig.createTacletIndex(),
            initConfig);
    }

    public Proof(Name name, org.key_project.prover.sequent.Sequent problem, InitConfig initConfig) {
        this(name, initConfig);
        final var rootNode = new Node(this, problem);
        final var firstGoal =
            new Goal(rootNode, initConfig.createTacletIndex(),
                initConfig.getServices());
        openGoals = openGoals.prepend(firstGoal);
        setRoot(rootNode);
    }

    public Services getServices() {
        return initConfig.getServices();
    }

    public Node getRoot() {
        return root;
    }

    public void setRoot(Node root) {
        this.root = root;
    }

    public String header() {
        return problemHeader;
    }

    public ImmutableList<Goal> getOpenGoals() {
        return openGoals;
    }

    public void setOpenGoals(ImmutableList<Goal> openGoals) {
        this.openGoals = openGoals;
    }

    public ImmutableList<Goal> getClosedGoals() {
        return closedGoals;
    }

    public void setClosedGoals(ImmutableList<Goal> closedGoals) {
        this.closedGoals = closedGoals;
    }

    public InitConfig getInitConfig() {
        return initConfig;
    }

    public void setInitConfig(InitConfig initConfig) {
        this.initConfig = initConfig;
    }

    @Override
    public @NonNull Name name() {
        return name;
    }


    public Node root() {
        return root;
    }

    /**
     * Returns the list of open goals.
     *
     * @return list with the open goals
     */
    @Override
    public @NonNull ImmutableList<@NonNull Goal> openGoals() {
        return openGoals;
    }

    /**
     * adds a list with new goals to the list of open goals
     *
     * @param goals the Iterable<Goal> to be prepended
     */
    @Override
    public void add(@NonNull Iterable<@NonNull Goal> goals) {
        ImmutableList<Goal> addGoals;
        if (goals instanceof ImmutableList<Goal> asList) {
            addGoals = asList;
        } else {
            addGoals = ImmutableList.fromList(goals);
        }
        add(addGoals);
    }

    /**
     * adds a list with new goals to the list of open goals
     *
     * @param goals the IList<Goal> to be prepended
     */
    public void add(ImmutableList<Goal> goals) {
        ImmutableList<Goal> newOpenGoals = openGoals.prepend(goals);
        if (openGoals != newOpenGoals) {
            openGoals = newOpenGoals;
        }
    }

    /**
     * removes the given goal and adds the new goals in list
     *
     * @param oldGoal the old goal that has to be removed from list
     * @param newGoals the Iterable<Goal> with the new goals that were result of a rule application
     *        on goal
     */
    @Override
    public void replace(Goal oldGoal, @NonNull Iterable<@NonNull Goal> newGoals) {
        openGoals = openGoals.removeAll(oldGoal);

        if (!closed()) {
            add(newGoals);
        }
    }

    /**
     * Close the given goals and all goals in the subtree below it.
     *
     * @param goalToClose the goal to close.
     */
    public void closeGoal(Goal goalToClose) {
        Node closedSubtree = goalToClose.getNode().close();

        boolean b = false;
        Iterator<Node> it = closedSubtree.leavesIterator();
        Goal goal;

        // close all goals below the given goalToClose
        while (it.hasNext()) {
            goal = getOpenGoal(it.next());
            if (goal != null) {
                b = true;
                // if (!GeneralSettings.noPruningClosed) {
                closedGoals = closedGoals.prepend(goal);
                // }
                remove(goal);
            }
        }

        if (b) {
            // For the moment it is necessary to fire the message ALWAYS
            // in order to detect branch closing.
            // fireProofGoalsAdded(ImmutableSLList.nil());
        }
    }

    /**
     * returns the goal that belongs to the given node or null if the node is an inner one
     *
     * @return the goal that belongs to the given node or null if the node is an inner one
     */
    public Goal getOpenGoal(Node node) {
        for (final Goal result : openGoals) {
            if (result.getNode() == node) {
                return result;
            }
        }
        return null;
    }

    /**
     * removes the given goal from the list of open goals. Take care removing the last goal will
     * fire the proofClosed event
     *
     * @param goal the Goal to be removed
     */
    private void remove(Goal goal) {
        ImmutableList<Goal> newOpenGoals = openGoals.removeAll(goal);
        if (newOpenGoals != openGoals) {
            openGoals = newOpenGoals;
        }
    }

    /**
     * returns true if the root node is marked as closed and all goals have been removed
     */
    public boolean closed() {
        return root.isClosed() && openGoals.isEmpty();
    }

    /**
     * Retrieves a bunch of statistics to the proof tree. This implementation traverses the proof
     * tree only once. Statistics are not cached; don't call this method too often.
     */
    public Statistics getStatistics() {
        return new Statistics(this);
    }

    /**
     * retrieves number of nodes
     */
    public int countNodes() {
        return root.countNodes();
    }

    /**
     * toString
     */
    @Override
    public String toString() {
        StringBuilder result = new StringBuilder();
        result.append("Proof -- ");
        if (!name.toString().isEmpty()) {
            result.append(name);
        } else {
            result.append("unnamed");
        }
        result.append("\nProoftree:\n");
        if (countNodes() < 50) {
            result.append(root.toString());
        } else {
            result.append("<too large to include>");
        }
        return result.toString();
    }

    public void dispose() {
        // TODO
    }

    /**
     * returns a collection of the namespaces valid for this proof
     */
    public NamespaceSet getNamespaces() {
        return getServices().getNamespaces();
    }
}
