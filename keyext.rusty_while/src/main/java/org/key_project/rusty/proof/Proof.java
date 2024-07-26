/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.Semisequent;
import org.key_project.rusty.logic.Sequent;
import org.key_project.rusty.logic.SequentFormula;
import org.key_project.rusty.proof.init.InitConfig;
import org.key_project.rusty.settings.ProofSettings;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;


public class Proof implements Named {
    /**
     * name of the proof
     */
    private final Name name;

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

    private Proof(String name, Sequent problem,
            InitConfig initConfig) {
        this(new Name(name), initConfig);

        final var rootNode = new Node(this, problem);
        final var firstGoal =
            new Goal(rootNode);
        openGoals = openGoals.prepend(firstGoal);
        setRoot(rootNode);
    }

    public Proof(String name, Term problem, InitConfig initConfig) {
        this(name,
            Sequent.createSuccSequent(
                new Semisequent(new SequentFormula(problem))),
            initConfig);
    }

    public Proof(Name name, Sequent problem, InitConfig initConfig) {
        this(name, initConfig);
        final var rootNode = new Node(this, problem);
        final var firstGoal =
            new Goal(rootNode);
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


}
