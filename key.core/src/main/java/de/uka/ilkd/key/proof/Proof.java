/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.beans.PropertyChangeListener;
import java.io.File;
import java.io.IOException;
import java.util.*;
import java.util.function.Consumer;
import java.util.function.Predicate;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import javax.swing.*;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.FileOrigin;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.io.IntermediateProofReplayer;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.ProofCorrectnessMgt;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.proof.replay.CopyingProofReplayer;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.merge.MergePartner;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.lookup.Lookup;


/**
 * A proof is represented as a tree whose nodes are created by applying rules on the current (open)
 * goals and dividing them up into several new subgoals. To distinguish between open goals (the ones
 * we are working on) and closed goals or inner nodes we restrict the use of the word goal to open
 * goals which are a subset of the proof tree's leaves. This proof class represents a proof and
 * encapsulates its tree structure. The {@link Goal} class represents a goal with all needed extra
 * information, and methods to apply rules. Furthermore, it offers services that deliver the open
 * goals, namespaces and several other information about the current state of the proof.
 */
public class Proof implements Named {

    /**
     * The time when the {@link Proof} instance was created.
     */
    final long creationTime = System.currentTimeMillis();

    /** name of the proof */
    private final Name name;

    /** the root of the proof */
    private Node root;

    /**
     * list with prooftree listeners of this proof attention: firing events makes use of array
     * list's random access nature
     */
    private final List<ProofTreeListener> listenerList = new LinkedList<>();

    /** list with the open goals of the proof */
    private ImmutableList<Goal> openGoals = ImmutableSLList.nil();

    /**
     * list with the closed goals of the proof, needed to make pruning in closed branches possible.
     * If the list needs too much memory, pruning can be disabled via the command line option
     * "--no-pruning-closed". In this case the list will not be filled.
     */
    private ImmutableList<Goal> closedGoals = ImmutableSLList.nil();

    /** declarations &c, read from a problem file or otherwise */
    private String problemHeader = "";

    /** the proof environment (optional) */
    private ProofEnvironment env;

    /** maps the Abbreviations valid for this proof to their corresponding terms. */
    private AbbrevMap abbreviations = new AbbrevMap();

    /** the logic configuration for this proof, i.e., logic signature, rules etc. */
    private InitConfig initConfig;

    /** the environment of the proof with specs and java model */
    private ProofCorrectnessMgt localMgt;

    /** settings valid independent of a proof */
    private final ProofIndependentSettings pis;
    /**
     * when different users load and save a proof this vector fills up with Strings containing the
     * usernames.
     */
    public List<String> userLog;

    /**
     * when load and save a proof with different versions of key this vector fills up with Strings
     * containing the GIT versions.
     */
    public List<String> keyVersionLog;

    private long autoModeTime = 0;

    private Strategy activeStrategy;

    private PropertyChangeListener settingsListener;

    /**
     * Set to true if the proof has been abandoned and the dispose method has been called on this
     * object.
     */
    private boolean disposed = false;

    /** list of rule app listeners */
    private final List<RuleAppListener> ruleAppListenerList =
        Collections.synchronizedList(new ArrayList<>(10));
    /**
     * Contains all registered {@link ProofDisposedListener}.
     */
    private final List<ProofDisposedListener> proofDisposedListener = new LinkedList<>();

    /**
     * The {@link File} under which this {@link Proof} was saved the last time if available or
     * {@code null} otherwise.
     */
    private File proofFile;

    @Nullable
    private Lookup userData;

    /**
     * Whether closing the proof should emit a {@link ProofEvent}.
     */
    private boolean mutedProofCloseEvents = false;

    /**
     * constructs a new empty proof with name
     */
    private Proof(Name name, InitConfig initConfig) {
        this.name = name;
        assert initConfig != null : "Tried to create proof without valid services.";
        this.initConfig = initConfig;

        if (initConfig.getSettings() == null) {
            // if no settings have been assigned yet, take default settings
            initConfig.setSettings(new ProofSettings(ProofSettings.DEFAULT_SETTINGS));
        }

        final Services services = this.initConfig.getServices();
        services.setProof(this);
        this.proofFile =
            services.getJavaModel() != null ? services.getJavaModel().getInitialFile() : null;

        settingsListener = config -> updateStrategyOnGoals();

        localMgt = new ProofCorrectnessMgt(this);

        initConfig.getSettings().getStrategySettings().addPropertyChangeListener(settingsListener);

        pis = ProofIndependentSettings.DEFAULT_INSTANCE;
    }

    /**
     * initialises the strategies
     */
    private void initStrategy() {
        StrategyProperties activeStrategyProperties =
            initConfig.getSettings().getStrategySettings().getActiveStrategyProperties();

        final Profile profile = getServices().getProfile();

        final Name strategy = initConfig.getSettings().getStrategySettings().getStrategy();
        if (profile.supportsStrategyFactory(strategy)) {
            setActiveStrategy(
                profile.getStrategyFactory(strategy).create(this, activeStrategyProperties));
        } else {
            setActiveStrategy(
                profile.getDefaultStrategyFactory().create(this, activeStrategyProperties));
        }
    }



    /** constructs a new empty proof with name */
    public Proof(String name, InitConfig initConfig) {
        this(new Name(name), initConfig);
    }

    private Proof(String name, Sequent problem, TacletIndex rules, BuiltInRuleIndex builtInRules,
            InitConfig initConfig) {
        this(new Name(name), initConfig);

        if (!ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings()
                .getUseOriginLabels()) {
            problem = OriginTermLabel.removeOriginLabels(problem, getServices()).sequent();
        }

        register(new ProofJavaSourceCollection(), ProofJavaSourceCollection.class);
        var rootNode = new Node(this, problem);
        var sources = lookup(ProofJavaSourceCollection.class);

        rootNode.sequent().forEach(formula -> {
            OriginTermLabel originLabel =
                (OriginTermLabel) formula.formula().getLabel(OriginTermLabel.NAME);
            if (originLabel != null) {
                if (originLabel.getOrigin() instanceof FileOrigin) {
                    ((FileOrigin) originLabel.getOrigin())
                            .getFileName()
                            .ifPresent(sources::addRelevantFile);
                }

                originLabel.getSubtermOrigins().stream()
                        .filter(o -> o instanceof FileOrigin)
                        .map(o -> (FileOrigin) o)
                        .forEach(o -> o.getFileName().ifPresent(sources::addRelevantFile));
            }
        });

        var firstGoal =
            new Goal(rootNode, rules, new BuiltInRuleAppIndex(builtInRules), getServices());
        openGoals = openGoals.prepend(firstGoal);
        setRoot(rootNode);

        if (closed()) {
            fireProofClosed();
        }
    }

    public Proof(String name, Term problem, String header, InitConfig initConfig, File proofFile) {
        this(name,
            Sequent.createSuccSequent(
                Semisequent.EMPTY_SEMISEQUENT.insert(0, new SequentFormula(problem)).semisequent()),
            initConfig.createTacletIndex(), initConfig.createBuiltInRuleIndex(), initConfig);
        problemHeader = header;
        this.proofFile = proofFile;
    }

    public Proof(String name, Term problem, String header, InitConfig initConfig) {
        this(name,
            Sequent.createSuccSequent(
                Semisequent.EMPTY_SEMISEQUENT.insert(0, new SequentFormula(problem)).semisequent()),
            initConfig.createTacletIndex(), initConfig.createBuiltInRuleIndex(), initConfig);
        problemHeader = header;
    }


    public Proof(String name, Sequent sequent, String header, TacletIndex rules,
            BuiltInRuleIndex builtInRules, InitConfig initConfig) {
        this(name, sequent, rules, builtInRules, initConfig);
        problemHeader = header;
    }


    /**
     * Cut off all reference such that it does not lead to a big memory leak if someone still holds
     * a reference to this proof object.
     */
    public void dispose() {
        if (isDisposed()) {
            return;
        }
        fireProofDisposing(new ProofDisposedEvent(this));
        clearAndDetachRuleAppIndexes();

        // Do required cleanup
        if (getServices() != null) {
            getServices().getSpecificationRepository().removeProof(this);
        }
        if (localMgt != null) {
            localMgt.removeProofListener(); // This is strongly required because the listener is
                                            // contained in a static List
        }
        // remove setting listener from settings
        initConfig.getSettings().getStrategySettings()
                .removePropertyChangeListener(settingsListener);
        // set every reference (except the name) to null
        root = null;
        env = null;
        openGoals = null;
        closedGoals = null;
        problemHeader = null;
        abbreviations = null;
        initConfig = null;
        localMgt = null;
        userLog = null;
        keyVersionLog = null;
        activeStrategy = null;
        settingsListener = null;
        disposed = true;
        userData = null;
        fireProofDisposed(new ProofDisposedEvent(this));
        // may now clean up proof disposed listeners too
        proofDisposedListener.clear();
    }


    /**
     * Returns true if the proof has been abandoned and the dispose method has been called on this
     * object. Should be asserted before proof object is accessed.
     */
    public boolean isDisposed() {
        return disposed;
    }


    /**
     * returns the name of the proof. Describes in short what has to be proved.
     *
     * @return the name of the proof
     */
    @Override
    public Name name() {
        return name;
    }


    public String header() {
        return problemHeader;
    }

    public ProofCorrectnessMgt mgt() {
        return localMgt;
    }

    /**
     * returns a collection of the namespaces valid for this proof
     */
    public NamespaceSet getNamespaces() {
        return getServices().getNamespaces();
    }

    /** returns the JavaInfo with the java type information */
    public JavaInfo getJavaInfo() {
        return getServices().getJavaInfo();
    }

    /** returns the Services with the java service classes */
    public Services getServices() {
        return initConfig.getServices();
    }

    public long getAutoModeTime() {
        return autoModeTime;
    }

    public void addAutoModeTime(long time) {
        autoModeTime += time;
    }



    /** sets the variable, function, sort, heuristics namespaces */
    public void setNamespaces(NamespaceSet ns) {
        getServices().setNamespaces(ns);
        if (!root.leaf()) {
            throw new IllegalStateException("Proof: ProgVars set too late");
        }

        Goal fstGoal = openGoals().head();
        fstGoal.makeLocalNamespacesFrom(ns);
    }

    public ProofEnvironment getEnv() {
        return env;
    }

    public void setEnv(ProofEnvironment env) {
        this.env = env;
    }

    public AbbrevMap abbreviations() {
        return abbreviations;
    }


    public Strategy getActiveStrategy() {
        if (activeStrategy == null) {
            initStrategy();
        }
        return activeStrategy;
    }


    public void setActiveStrategy(Strategy activeStrategy) {
        this.activeStrategy = activeStrategy;
        getSettings().getStrategySettings().setStrategy(activeStrategy.name());
        updateStrategyOnGoals();

        // This could be seen as a hack; it's however important that OSS is
        // refreshed after strategy has been set, otherwise nothing will happen.
        OneStepSimplifier.refreshOSS(root.proof());
    }


    private void updateStrategyOnGoals() {
        Strategy ourStrategy = getActiveStrategy();

        for (Goal goal : openGoals()) {
            goal.setGoalStrategy(ourStrategy);
        }
    }


    public void clearAndDetachRuleAppIndexes() {
        // Taclet indices of the particular goals have to
        // be rebuilt
        for (Goal goal : openGoals()) {
            goal.clearAndDetachRuleAppIndex();
        }
    }


    /**
     * returns the root node of the proof
     */
    public Node root() {
        return root;
    }


    /** sets the root of the proof */
    public void setRoot(Node root) {
        if (this.root != null) {
            throw new IllegalStateException("Tried to reset the root of the proof.");
        } else {
            this.root = root;
            fireProofStructureChanged();
        }
    }


    public ProofSettings getSettings() {
        return initConfig.getSettings();
    }

    public ProofIndependentSettings getProofIndependentSettings() {
        return pis;
    }

    /**
     * Returns the list of open goals.
     *
     * @return list with the open goals
     */
    public ImmutableList<Goal> openGoals() {
        return openGoals;
    }

    /**
     * Returns the list of closed goals, needed to make pruning in closed branches possible. If the
     * list needs too much memory, pruning can be disabled via the command line option
     * "--no-pruning-closed". In this case the list will not be filled.
     *
     * @return list with the closed goals
     */
    public ImmutableList<Goal> closedGoals() {
        return closedGoals;
    }

    /**
     * Returns the list of all, open and closed, goals.
     *
     * @return list with all goals.
     *
     * @see #openGoals()
     * @see #closedGoals()
     */
    public ImmutableList<Goal> allGoals() {
        return openGoals.size() < closedGoals.size() ? closedGoals.prepend(openGoals)
                : openGoals.prepend(closedGoals);
    }

    /**
     * return the list of open and enabled goals
     *
     * @return list of open and enabled goals, never null
     * @author mulbrich
     */
    public ImmutableList<Goal> openEnabledGoals() {
        return filterEnabledGoals(openGoals);
    }


    /**
     * filter those goals from a list which are enabled
     *
     * @param goals non-null list of goals
     * @return sublist such that every goal in the list is enabled
     * @see Goal#isAutomatic()
     * @author mulbrich
     */
    private ImmutableList<Goal> filterEnabledGoals(ImmutableList<Goal> goals) {
        ImmutableList<Goal> enabledGoals = ImmutableSLList.nil();
        for (Goal g : goals) {
            if (g.isAutomatic() && !g.isLinked()) {
                enabledGoals = enabledGoals.prepend(g);
            }
        }
        return enabledGoals;
    }


    /**
     * removes the given goal and adds the new goals in list
     *
     * @param oldGoal the old goal that has to be removed from list
     * @param newGoals the IList<Goal> with the new goals that were result of a rule application on
     *        goal
     */
    public void replace(Goal oldGoal, ImmutableList<Goal> newGoals) {
        openGoals = openGoals.removeAll(oldGoal);

        if (closed()) {
            fireProofClosed();
        } else {
            fireProofGoalRemoved(oldGoal);
            add(newGoals);
        }
    }


    /**
     * Close the given goals and all goals in the subtree below it.
     *
     * @param goalToClose the goal to close.
     */
    public void closeGoal(Goal goalToClose) {

        Node closedSubtree = goalToClose.node().close();

        boolean b = false;
        Iterator<Node> it = closedSubtree.leavesIterator();
        Goal goal;

        // close all goals below the given goalToClose
        while (it.hasNext()) {
            goal = getOpenGoal(it.next());
            if (goal != null) {
                b = true;
                if (!GeneralSettings.noPruningClosed) {
                    closedGoals = closedGoals.prepend(goal);
                }
                remove(goal);
            }
        }

        if (b) {
            // For the moment it is necessary to fire the message ALWAYS
            // in order to detect branch closing.
            fireProofGoalsAdded(ImmutableSLList.nil());
        }
    }

    /**
     * Opens a previously closed node (the one corresponding to p_goal) and all its closed parents.
     * <p>
     *
     * This is, for instance, needed for the {@link MergeRule}: In a situation where a merge node
     * and its associated partners have been closed and the merge node is then pruned away, the
     * partners have to be reopened again. Otherwise, we have a soundness issue.
     * <p>
     * This will automatically add the goal to the list of open goals.
     * </p>
     *
     * @param goal The goal to be opened again.
     */
    public void reOpenGoal(Goal goal) {
        add(goal);
        goal.node().reopen();
        closedGoals = closedGoals.removeAll(goal);
        fireProofStructureChanged();
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
            if (closed()) {
                fireProofClosed();
            } else {
                fireProofGoalRemoved(goal);
            }
        }
    }

    /**
     * adds a new goal to the list of goals
     *
     * @param goal the Goal to be added
     *
     * @deprecated use {@link #reOpenGoal(Goal)} when re-opening a goal
     */
    @Deprecated // eventually, this method should be made private
    public void add(Goal goal) {
        ImmutableList<Goal> newOpenGoals = openGoals.prepend(goal);
        if (openGoals != newOpenGoals) {
            openGoals = newOpenGoals;
            fireProofGoalsAdded(goal);
        }
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

        // For the moment it is necessary to fire the message ALWAYS
        // in order to detect branch closing.
        fireProofGoalsAdded(goals);
    }


    /**
     * returns true if the root node is marked as closed and all goals have been removed
     */
    public boolean closed() {
        return root.isClosed() && openGoals.isEmpty();
    }

    /**
     * For all nodes in this proof: set the step index according to their position in the tree.
     */
    public void setStepIndices() {
        int stepIndex = 0;
        Iterator<Node> nodeIterator = this.root().subtreeIterator();
        while (nodeIterator.hasNext()) {
            Node node = nodeIterator.next();
            node.setStepIndex(stepIndex);
            stepIndex++;
        }
    }


    /**
     * This class is responsible for pruning a proof tree at a certain cutting point. It has been
     * introduced to encapsulate the methods that are needed for pruning. Since the class has
     * influence on the internal state of the proof it should not be moved to a new file, in order
     * to restrict the access to it.
     */
    private class ProofPruner {
        private Node firstLeaf = null;

        public ImmutableList<Node> prune(final Node cuttingPoint) {

            // there is only one leaf containing an open goal that is interesting for pruning the
            // subtree of <code>node</code>, namely the first leave that is found by a breadth
            // first search.
            // The other leaves containing open goals are only important for removing the open goals
            // from the open goal list.
            // To that end, those leaves are stored in residualLeaves. For increasing the
            // performance,
            // a tree structure has been chosen, because it offers the operation
            // <code>contains</code> in O(log n).
            final Set<Node> residualLeaves = new TreeSet<>(Comparator.comparingInt(Node::serialNr));


            // First, make a breadth first search, in order to find the leaf
            // with the shortest distance to the cutting point and to remove
            // the rule applications from the proof management system.
            // Furthermore, store the residual leaves.
            breadthFirstSearch(cuttingPoint, (proof, visitedNode) -> {
                if (visitedNode.leaf()) {
                    // pruning in closed branches (can be disabled via "--no-pruning-closed")
                    if (!visitedNode.isClosed() || !GeneralSettings.noPruningClosed) {
                        if (firstLeaf == null) {
                            firstLeaf = visitedNode;
                        } else {
                            residualLeaves.add(visitedNode);
                        }
                    }
                }

                if (initConfig != null && visitedNode.parent() != null) {
                    Proof.this.mgt().ruleUnApplied(visitedNode.parent().getAppliedRuleApp());
                    for (final NoPosTacletApp app : visitedNode.parent()
                            .getLocalIntroducedRules()) {
                        initConfig.getJustifInfo().removeJustificationFor(app.taclet());
                    }
                }

                // Merge rule applications: Unlink all merge partners.
                if (visitedNode.getAppliedRuleApp() instanceof MergeRuleBuiltInRuleApp) {
                    final MergeRuleBuiltInRuleApp mergeApp =
                        (MergeRuleBuiltInRuleApp) visitedNode.getAppliedRuleApp();

                    for (MergePartner mergePartner : mergeApp.getMergePartners()) {
                        final Goal linkedGoal = mergePartner.getGoal();

                        if (linkedGoal.node().isClosed()) {
                            // The partner node has already been closed; we
                            // have to add the goal again.
                            proof.reOpenGoal(linkedGoal);
                        }

                        linkedGoal.setLinkedGoal(null);
                        SwingUtilities.invokeLater(() -> pruneProof(linkedGoal));
                    }
                }
            });

            // first leaf is closed -> add as goal and reopen
            final Goal firstGoal =
                firstLeaf.isClosed() ? getClosedGoal(firstLeaf) : getOpenGoal(firstLeaf);
            assert firstGoal != null;
            if (firstLeaf.isClosed()) {
                reOpenGoal(firstGoal);
            }

            // TODO: WP: test interplay with merge rules
            // Cutting a linked goal (linked by a "defocusing" merge
            // operation, see {@link MergeRule}) unlinks this goal again.
            if (firstGoal.isLinked()) {
                firstGoal.setLinkedGoal(null);
            }

            // Go from the first leaf that has been found to the cutting point. For each node on the
            // path,
            // remove the local rules from firstGoal that have been added by the considered node.
            traverseFromChildToParent(firstLeaf, cuttingPoint, (proof, visitedNode) -> {
                for (final NoPosTacletApp app : visitedNode.getLocalIntroducedRules()) {
                    firstGoal.ruleAppIndex().removeNoPosTacletApp(app);
                    initConfig.getJustifInfo().removeJustificationFor(app.taclet());
                }

                firstGoal.pruneToParent();

                final List<StrategyInfoUndoMethod> undoMethods =
                    visitedNode.getStrategyInfoUndoMethods();
                for (StrategyInfoUndoMethod undoMethod : undoMethods) {
                    firstGoal.undoStrategyInfoAdd(undoMethod);
                }
            });


            // do some cleaning and refreshing: Clearing indices, caches....
            refreshGoal(firstGoal, cuttingPoint);

            // cut the subtree, it is not needed anymore.
            ImmutableList<Node> subtrees = cut(cuttingPoint);


            // remove the goals of the residual leaves.
            removeOpenGoals(residualLeaves);
            removeClosedGoals(residualLeaves);

            /*
             * this ensures that the open goals are in interactive mode and thus all rules are
             * available in the just pruned goal (see GitLab #1480)
             */
            setRuleAppIndexToInteractiveMode();

            return subtrees;

        }

        private void refreshGoal(Goal goal, Node node) {
            goal.getRuleAppManager().clearCache();
            goal.ruleAppIndex().clearIndexes();
            goal.node().setAppliedRuleApp(null);
            node.clearNameCache();

            // delete NodeInfo, but preserve potentially existing branch label
            String branchLabel = node.getNodeInfo().getBranchLabel();
            node.clearNodeInfo();
            if (branchLabel != null) {
                node.getNodeInfo().setBranchLabel(branchLabel);
            }
        }

        private void removeOpenGoals(Collection<Node> toBeRemoved) {
            ImmutableList<Goal> newGoalList = ImmutableSLList.nil();
            for (Goal openGoal : openGoals) {
                if (!toBeRemoved.contains(openGoal.node())) {
                    newGoalList = newGoalList.append(openGoal);
                }
            }
            openGoals = newGoalList;
        }

        /**
         * Removes the given collection of Nodes from the closedGoals. Nodes in the given collection
         * which are not member of closedGoals are ignored. This method does not reopen the goals!
         * This has to be done via the method reOpenGoal() if desired.
         *
         * @param toBeRemoved the goals to remove
         */
        private void removeClosedGoals(Collection<Node> toBeRemoved) {
            ImmutableList<Goal> newGoalList = ImmutableSLList.nil();
            for (Goal closedGoal : closedGoals) {
                if (!toBeRemoved.contains(closedGoal.node())) {
                    newGoalList = newGoalList.prepend(closedGoal);
                }
            }
            closedGoals = newGoalList;
        }

        private ImmutableList<Node> cut(Node node) {
            ImmutableList<Node> children = ImmutableSLList.nil();
            Iterator<Node> it = node.childrenIterator();

            while (it.hasNext()) {
                children = children.append(it.next());

            }
            for (Node child : children) {
                node.remove(child);
            }
            return children;
        }

    }

    /**
     * Performs an undo operation on the given goal. This is equivalent to a pruning of the parent
     * node of the goal (if this parent node exists).
     *
     * @param goal the Goal where the last rule application gets undone
     */
    public synchronized void pruneProof(Goal goal) {
        if (goal.node().parent() != null) {
            pruneProof(goal.node().parent());
        }
    }

    /**
     * Prunes the subtree beneath the node <code>cuttingPoint</code>, i.e. the node
     * <code>cuttingPoint</code> remains as the last node on the branch. As a result, an open goal
     * is associated with this node.
     *
     * @param cuttingPoint node below which to prune
     * @return the subtrees that have been pruned.
     */
    public synchronized ImmutableList<Node> pruneProof(Node cuttingPoint) {
        return pruneProof(cuttingPoint, true);
    }

    public synchronized ImmutableList<Node> pruneProof(Node cuttingPoint, boolean fireChanges) {
        assert cuttingPoint.proof() == this;
        if (getOpenGoal(cuttingPoint) != null) {
            return null;
        }
        // abort pruning if the node is closed and pruning in closed branches is disabled
        if (cuttingPoint.isClosed() && GeneralSettings.noPruningClosed) {
            return null;
        }

        ProofPruner pruner = new ProofPruner();
        if (fireChanges) {
            fireProofIsBeingPruned(cuttingPoint);
        }
        ImmutableList<Node> result = pruner.prune(cuttingPoint);
        if (fireChanges) {
            fireProofGoalsChanged();
            fireProofPruned(cuttingPoint);
        }
        return result;
    }

    /**
     * Makes a downwards directed breadth first search on the proof tree, starting with node
     * <code>startNode</code>. The visited notes are reported to the object <code>visitor</code>.
     * The first reported node is <code>startNode</code>.
     */
    public void breadthFirstSearch(Node startNode, ProofVisitor visitor) {
        ArrayDeque<Node> queue = new ArrayDeque<>();
        queue.add(startNode);
        while (!queue.isEmpty()) {
            Node currentNode = queue.poll();
            Iterator<Node> it = currentNode.childrenIterator();
            while (it.hasNext()) {
                queue.add(it.next());
            }
            visitor.visit(this, currentNode);
        }
    }


    /**
     * Bread-first search for the first node, that matches the given predicate.
     *
     * @param pred non-null test function
     * @return a node fulfilling {@code pred} or null
     */
    public @Nullable Node findAny(@Nonnull Predicate<Node> pred) {
        Queue<Node> queue = new LinkedList<>();
        queue.add(root);
        while (!queue.isEmpty()) {
            Node cur = queue.poll();
            if (pred.test(cur)) {
                return cur;
            }
            Iterator<Node> iter = cur.childrenIterator();
            while (iter.hasNext()) {
                queue.add(iter.next());
            }
        }
        return null;
    }


    public void traverseFromChildToParent(Node child, Node parent, ProofVisitor visitor) {
        do {
            visitor.visit(this, child);
            child = child.parent();
        } while (child != parent);
    }

    /** fires the event that the proof has been expanded at the given node */
    public void fireProofExpanded(Node node) {
        ProofTreeEvent e = new ProofTreeEvent(this, node);
        synchronized (listenerList) {
            for (ProofTreeListener listener : listenerList) {
                listener.proofExpanded(e);
            }
        }
    }

    /** fires the event that the proof is being pruned at the given node */
    protected void fireProofIsBeingPruned(Node below) {
        ProofTreeEvent e = new ProofTreeEvent(this, below);
        synchronized (listenerList) {
            for (ProofTreeListener listener : listenerList) {
                listener.proofIsBeingPruned(e);
            }
        }
    }

    /** fires the event that the proof has been pruned at the given node */
    protected void fireProofPruned(Node below) {
        ProofTreeEvent e = new ProofTreeEvent(this, below);
        synchronized (listenerList) {
            for (ProofTreeListener listener : listenerList) {
                listener.proofPruned(e);
            }
        }
    }


    /** fires the event that the proof has been restructured */
    public void fireProofStructureChanged() {
        ProofTreeEvent e = new ProofTreeEvent(this);
        synchronized (listenerList) {
            for (ProofTreeListener listener : listenerList) {
                listener.proofStructureChanged(e);
            }
        }
    }


    /** fires the event that a goal has been removed from the list of goals */
    protected void fireProofGoalRemoved(Goal goal) {
        ProofTreeEvent e = new ProofTreeEvent(this, goal);
        synchronized (listenerList) {
            for (ProofTreeListener listener : listenerList) {
                listener.proofGoalRemoved(e);
            }
        }
    }


    /**
     * fires the event that new goals have been added to the list of goals
     */
    protected void fireProofGoalsAdded(ImmutableList<Goal> goals) {
        ProofTreeEvent e = new ProofTreeEvent(this, goals);
        synchronized (listenerList) {
            for (ProofTreeListener listener : listenerList) {
                listener.proofGoalsAdded(e);
            }
        }
    }


    /**
     * fires the event that new goals have been added to the list of goals
     */
    protected void fireProofGoalsAdded(Goal goal) {
        fireProofGoalsAdded(ImmutableSLList.<Goal>nil().prepend(goal));
    }


    /** fires the event that the proof has been restructured */
    public void fireProofGoalsChanged() {
        ProofTreeEvent e = new ProofTreeEvent(this, openGoals());
        synchronized (listenerList) {
            for (ProofTreeListener listener : listenerList) {
                listener.proofGoalsChanged(e);
            }
        }
    }


    /**
     * fires the event that the proof has closed. This event fired instead of the proofGoalRemoved
     * event when the last goal in list is removed.
     */
    protected void fireProofClosed() {
        if (mutedProofCloseEvents) {
            return;
        }
        ProofTreeEvent e = new ProofTreeEvent(this);
        synchronized (listenerList) {
            for (ProofTreeListener listener : listenerList) {
                listener.proofClosed(e);
            }
        }
    }

    /**
     * Fires the event {@link ProofTreeListener#notesChanged(ProofTreeEvent)} to all listener.
     *
     * @param node The changed {@link Node}.
     */
    protected void fireNotesChanged(Node node) {
        ProofTreeEvent e = new ProofTreeEvent(this, node);
        synchronized (listenerList) {
            for (ProofTreeListener listener : listenerList) {
                listener.notesChanged(e);
            }
        }
    }


    /**
     * adds a listener to the proof
     *
     * @param listener the ProofTreeListener to be added
     */
    public synchronized void addProofTreeListener(ProofTreeListener listener) {
        synchronized (listenerList) {
            listenerList.add(listener);
        }
    }


    /**
     * removes a listener from the proof
     *
     * @param listener the ProofTreeListener to be removed
     */
    public synchronized void removeProofTreeListener(ProofTreeListener listener) {
        synchronized (listenerList) {
            listenerList.remove(listener);
        }
    }


    public synchronized boolean containsProofTreeListener(ProofTreeListener listener) {
        synchronized (listenerList) {
            return listenerList.contains(listener);
        }
    }


    /**
     * returns true if the given node is part of a Goal
     *
     * @return true if the given node is part of a Goal
     */
    public boolean isOpenGoal(Node node) {
        return getOpenGoal(node) != null;
    }


    /**
     * returns the goal that belongs to the given node or null if the node is an inner one
     *
     * @return the goal that belongs to the given node or null if the node is an inner one
     */
    public Goal getOpenGoal(Node node) {
        for (final Goal result : openGoals) {
            if (result.node() == node) {
                return result;
            }
        }
        return null;
    }

    /**
     * @param node the Node which is checked for a corresponding closed goal
     * @return true if the goal that belongs to the given node is closed and false if not or if
     *         there is no such goal.
     */
    public boolean isClosedGoal(Node node) {
        return getClosedGoal(node) != null;
    }

    /**
     * Get the closed goal belonging to the given node if it exists.
     *
     * @param node the Node where a corresponding closed goal is searched
     * @return the closed goal that belongs to the given node or null if the node is an inner one or
     *         an open goal
     */
    public Goal getClosedGoal(Node node) {
        for (final Goal result : closedGoals) {
            if (result.node() == node) {
                return result;
            }
        }
        return null;
    }

    /**
     * returns the list of goals of the subtree starting with node.
     *
     * @param node the Node where to start from
     * @return the list of goals of the subtree starting with node
     */

    public ImmutableList<Goal> getSubtreeGoals(Node node) {
        return getGoalsBelow(node, openGoals);
    }

    /**
     * Returns a list of all (closed) goals of the closed subtree pending from this node.
     *
     * @param node the root of the subtree
     * @return the closed goals in the subtree
     */
    public ImmutableList<Goal> getClosedSubtreeGoals(Node node) {
        return getGoalsBelow(node, closedGoals);
    }

    /**
     * Returns a list of all goals from the provided list that are associated to goals below
     * <code>node</code>
     *
     * @param node the root of the subtree
     * @param fromGoals the list of goals from which to select
     * @return the goals below node that are contained in <code>fromGoals</code>
     */
    private static ImmutableList<Goal> getGoalsBelow(Node node, ImmutableList<Goal> fromGoals) {
        ImmutableList<Goal> result = ImmutableSLList.nil();
        List<Node> leaves = node.getLeaves();
        for (final Goal goal : fromGoals) {
            // if list contains node, remove it to make the list faster later
            if (leaves.remove(goal.node())) {
                result = result.prepend(goal);
            }
        }
        return result;
    }

    /**
     * get the list of goals of the subtree starting with node which are enabled.
     *
     * @param node the Node where to start from
     * @return the list of enabled goals of the subtree starting with node
     */
    public ImmutableList<Goal> getSubtreeEnabledGoals(Node node) {
        return filterEnabledGoals(getSubtreeGoals(node));
    }

    /**
     * returns true iff the given node is found in the proof tree
     *
     * @param node the Node to search for
     * @return true iff the given node is found in the proof tree
     */
    public boolean find(Node node) {
        if (root == null) {
            return false;
        }
        return root.find(node);
    }


    /**
     * retrieves number of nodes
     */
    public int countNodes() {
        return root.countNodes();
    }


    /**
     * Currently the rule app index can either operate in interactive mode (and contain applications
     * of all existing taclets) or in automatic mode (and only contain a restricted set of taclets
     * that can possibly be applied automated). This distinction could be replaced with a more
     * general way to control the contents of the rule app index
     */
    public void setRuleAppIndexToAutoMode() {
        for (final Goal g : openGoals) {
            g.ruleAppIndex().autoModeStarted();
        }
    }


    public void setRuleAppIndexToInteractiveMode() {
        for (final Goal g : openGoals) {
            g.ruleAppIndex().autoModeStopped();
        }
    }

    /**
     * retrieves number of branches
     */
    public int countBranches() {
        return root.countBranches();
    }

    /**
     * Retrieves a bunch of statistics to the proof tree. This implementation traverses the proof
     * tree only once. Statistics are not cached; don't call this method too often.
     */
    public Statistics getStatistics() {
        return new Statistics(this);
    }

    /** toString */
    @Override
    public String toString() {
        StringBuilder result = new StringBuilder();
        result.append("Proof -- ");
        if (!"".equals(name.toString())) {
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

    /** fires the event that a rule has been applied */
    protected void fireRuleApplied(ProofEvent p_e) {
        synchronized (ruleAppListenerList) {
            for (RuleAppListener ral : ruleAppListenerList) {
                ral.ruleApplied(p_e);
            }
        }
    }

    public void addRuleAppListener(RuleAppListener p) {
        if (p == null) {
            return;
        }
        synchronized (ruleAppListenerList) {
            ruleAppListenerList.add(p);
        }
    }

    public void removeRuleAppListener(RuleAppListener p) {
        synchronized (ruleAppListenerList) { // TODO (DS, 2019-03-19): Is null for SET tests!?!
            ruleAppListenerList.remove(p);
        }
    }

    /**
     * Registers the given {@link ProofDisposedListener}.
     *
     * @param l The {@link ProofDisposedListener} to register.
     */
    public void addProofDisposedListener(ProofDisposedListener l) {
        if (l != null) {
            proofDisposedListener.add(l);
        }
    }

    /**
     * Registers the given {@link ProofDisposedListener} to run before all previously registered
     * listeners.
     *
     * @param l The {@link ProofDisposedListener} to register.
     */
    public void addProofDisposedListenerFirst(ProofDisposedListener l) {
        if (l != null) {
            proofDisposedListener.add(0, l);
        }
    }

    /**
     * Unregisters the given {@link ProofDisposedListener}.
     *
     * @param l The {@link ProofDisposedListener} to unregister.
     */
    public void removeProofDisposedListener(ProofDisposedListener l) {
        if (l != null) {
            proofDisposedListener.remove(l);
        }
    }

    /**
     * Returns all registered {@link ProofDisposedListener}.
     *
     * @return All registered {@link ProofDisposedListener}.
     */
    public ProofDisposedListener[] getProofDisposedListeners() {
        return proofDisposedListener
                .toArray(new ProofDisposedListener[0]);
    }

    /**
     * Fires the event {@link ProofDisposedListener#proofDisposed(ProofDisposedEvent)} to all
     * listener.
     *
     * @param e The event to fire.
     */
    protected void fireProofDisposed(ProofDisposedEvent e) {
        ProofDisposedListener[] listener = getProofDisposedListeners();
        for (ProofDisposedListener l : listener) {
            l.proofDisposed(e);
        }
    }

    /**
     * Fires the event {@link ProofDisposedListener#proofDisposing(ProofDisposedEvent)} to all
     * listener.
     *
     * @param e The event to fire.
     */
    protected void fireProofDisposing(ProofDisposedEvent e) {
        ProofDisposedListener[] listener = getProofDisposedListeners();
        for (ProofDisposedListener l : listener) {
            l.proofDisposing(e);
        }
    }

    public InitConfig getInitConfig() {
        return initConfig;
    }

    /**
     * Returns the {@link File} under which the {@link Proof} was saved the last time if available.
     *
     * @return The {@link File} under which the {@link Proof} was saved the last time or
     *         {@code null} if not available.
     */
    public File getProofFile() {
        return proofFile;
    }

    /**
     * Sets the {@link File} under which the {@link Proof} was saved the last time.
     *
     * @param proofFile The {@link File} under which the {@link Proof} was saved the last time.
     */
    public void setProofFile(File proofFile) {
        this.proofFile = proofFile;
    }

    public void saveToFile(File file) throws IOException {
        ProofSaver saver = new ProofSaver(this, file);
        saver.save();
    }

    /**
     * Save this proof to a file whilst omitting all proof steps.
     * In effect, this only saves the proof obligation.
     *
     * @param file file to save proof in
     * @throws IOException on any I/O error
     */
    public void saveProofObligationToFile(File file) throws IOException {
        ProofSaver saver = new ProofSaver(this, file, false);
        saver.save();
    }

    /**
     *
     * @return the current profile's factory for the active strategy, or the default factory if
     *         there is no active strategy.
     * @see Profile#getStrategyFactory(Name)
     * @see #getActiveStrategy()
     */
    public StrategyFactory getActiveStrategyFactory() {
        Name activeStrategyName = getActiveStrategy() != null ? getActiveStrategy().name() : null;
        return activeStrategyName != null
                ? getServices().getProfile().getStrategyFactory(activeStrategyName)
                : getServices().getProfile().getDefaultStrategyFactory();

    }

    /**
     * Retrieves a user-defined data.
     *
     * @param service the class for which the data were registered
     * @param <T> any class
     * @return null or the previous data
     * @see #register(Object, Class)
     */
    public <T> T lookup(Class<T> service) {
        try {
            if (userData == null) {
                return null;
            }
            return userData.get(service);
        } catch (IllegalStateException ignored) {
            return null;
        }
    }

    /**
     * Register a user-defined data in this node info.
     *
     * @param obj an object to be registered
     * @param service the key under it should be registered
     * @param <T> type of the object to register
     */
    public <T> void register(T obj, Class<T> service) {
        getUserData().register(obj, service);
    }

    /**
     * Remove a previous registered user-defined data.
     *
     * @param obj registered object
     * @param service the key under which the data was registered
     * @param <T> type of the object to unregister
     */
    public <T> void deregister(T obj, Class<T> service) {
        if (userData != null) {
            userData.deregister(obj, service);
        }
    }

    /**
     * Get the associated lookup of user-defined data.
     *
     * @return the associated lookup
     */
    public @Nonnull Lookup getUserData() {
        if (userData == null) {
            userData = new Lookup();
        }
        return userData;
    }

    public void setMutedProofCloseEvents(boolean mutedProofCloseEvents) {
        this.mutedProofCloseEvents = mutedProofCloseEvents;
    }

    /**
     * For each branch closed by reference to another proof,
     * copy the relevant proof steps into this proof.
     *
     * @param referencedFrom filter, if not null copy only from that proof
     * @param callbackTotal callback that gets the total number of branches to complete
     * @param callbackBranch callback notified every time a branch has been copied
     */
    public void copyCachedGoals(Proof referencedFrom, Consumer<Integer> callbackTotal,
            Runnable callbackBranch) {
        // first, ensure that all cached goals are copied over
        List<Goal> goals = closedGoals().toList();
        List<Goal> todo = new ArrayList<>();
        for (Goal g : goals) {
            Node node = g.node();
            ClosedBy c = node.lookup(ClosedBy.class);
            if (c == null) {
                continue;
            }
            if (referencedFrom != null && referencedFrom != c.getProof()) {
                continue;
            }
            todo.add(g);
        }
        if (callbackTotal != null) {
            callbackTotal.accept(todo.size());
        }
        for (Goal g : todo) {
            reOpenGoal(g);
            ClosedBy c = g.node().lookup(ClosedBy.class);
            g.node().deregister(c, ClosedBy.class);
            try {
                new CopyingProofReplayer(c.getProof(), this).copy(c.getNode(), g);
            } catch (IntermediateProofReplayer.BuiltInConstructionException e) {
                throw new RuntimeException(e);
            }
            if (callbackBranch != null) {
                callbackBranch.run();
            }
        }
    }
}
