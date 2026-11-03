/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.prover.impl;

import java.util.Iterator;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;

import org.key_project.prover.engine.GoalChooser;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


/**
 * Helper class for managing a list of goals on which rules are applied. The class provides methods
 * for removing a goal, and for updating the internal data structures after a rule has been applied.
 * <p>
 * The {@code GoalChooser} interface binds its proof and goal type parameters to non-null
 * {@code ProofObject}/{@code ProofGoal} bounds, but this chooser may be initialised without a
 * proof or goals (see {@link #init}); the generic-bound artifact is suppressed with a scoped key.
 */
@NullMarked
@SuppressWarnings("nullness:type.argument.type.incompatible")
public class DefaultGoalChooser implements GoalChooser<@Nullable Proof, @Nullable Goal> {

    /** the proof that is worked with */
    protected @Nullable Proof proof;

    /** list of goals on which the strategy should be applied */
    protected ImmutableList<Goal> goalList = ImmutableList.nil();

    /** part of goalList that should be worked on next */
    protected ImmutableList<Goal> nextGoals = ImmutableList.nil();

    /** true iff all goals have satisfiable constraints */
    protected boolean allGoalsSatisfiable = false;

    /**
     * Subset of the goals to which currently taclets are applied. First this is the list of goals
     * with unsatisfiable constraints, later this is a subset of the goals having inconsistent
     * constraints
     */
    protected ImmutableList<Goal> selectedList = ImmutableList.nil();

    protected @Nullable Node currentSubtreeRoot = null;

    public DefaultGoalChooser() {
    }

    /**
     * {@inheritDoc}
     *
     * The {@code GoalChooser} interface binds its goal type parameter to
     * {@code @Nullable ProofGoal} (generic-bound artifact), so it requires a
     * {@code @Nullable Goal} list element here; the implementation only ever
     * handles non-null goals, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:override.param.invalid")
    public void init(@Nullable Proof p_proof, @Nullable ImmutableList<Goal> p_goals) {
        if (p_proof == null && !(p_goals == null || p_goals.isEmpty())) {
            throw new RuntimeException("A not existing proof has goals. This makes no sense.");
        }
        allGoalsSatisfiable = p_goals == null || p_goals.isEmpty();
        currentSubtreeRoot = null;
        if (p_proof != proof) {
            if (proof != null) {
                proof.removeProofTreeListener(proofTreeListener);
            }
            if (p_proof != null) {
                p_proof.addProofTreeListener(proofTreeListener);
            }
        }
        proof = p_proof;
        setupGoals(p_goals == null ? ImmutableList.nil() : p_goals);
    }

    /**
     * Sets up the goal list from the given goals and the configured proof.
     *
     * @param p_goals The goals to show.
     *        <p>
     *        The proof is initialized before goals are set up; the dereference of the (nullable)
     *        proof
     *        field is suppressed with a scoped key. The root lookup is part of the same invariant:
     *        the proof of an active goal chooser always has its root node, so passing {@code
     *        proof.root()} to {@link #findMinimalSubtreeBelow(Node)} is suppressed with a scoped
     *        key.
     */
    @SuppressWarnings({ "nullness:dereference.of.nullable",
        "nullness:argument.type.incompatible" })
    protected void setupGoals(ImmutableList<Goal> p_goals) {
        goalList = ImmutableList.nil();
        selectedList = ImmutableList.nil();
        nextGoals = ImmutableList.nil();

        if (allGoalsSatisfiable) {
            goalList = p_goals;
            if (currentSubtreeRoot != null) {
                findMinimalSubtree(currentSubtreeRoot);
            }
        } else {

            for (final Goal goal : p_goals) {
                selectedList = selectedList.prepend(goal);
            }

            allGoalsSatisfiable = selectedList.isEmpty();

            if (allGoalsSatisfiable) {
                findMinimalSubtreeBelow(proof.root());
            }
        }
    }

    private final ProofTreeObserver proofTreeListener = new ProofTreeObserver();

    /** Important when a proof is pruned */
    class ProofTreeObserver extends ProofTreeAdapter {
        /**
         * The proof tree has been pruned under the node mentioned in the ProofTreeEvent. In other
         * words, that node should no longer have any children now. Any nodes that were not
         * descendants of that node are unaffected.
         * <p>
         * The proof is initialized while the goal chooser is active; the dereference of the
         * (nullable) proof field is suppressed with a scoped key. The root lookup is part of the
         * same invariant: pruning never removes the proof root, so passing {@code proof.root()} to
         * {@code getSubtreeGoals} is suppressed with a scoped key.
         */
        @Override
        @SuppressWarnings({ "nullness:dereference.of.nullable",
            "nullness:argument.type.incompatible" })
        public void proofPruned(ProofTreeEvent e) {
            currentSubtreeRoot = e.getNode();
            setupGoals(proof.getSubtreeGoals(proof.root()));
        }
    }


    protected int nextGoalCounter = 0;

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.proof.IGoalChooser#getNextGoal()
     */
    public @Nullable Goal getNextGoal() {
        Goal result;

        if (allGoalsSatisfiable) {
            if (nextGoals.isEmpty()) {
                nextGoals = selectedList;
            }

            if (nextGoals.isEmpty()) {
                result = null;
            } else {
                result = nextGoals.head();
                nextGoals = nextGoals.tail();
            }
        } else {
            ++nextGoalCounter;
            if (nextGoalCounter % 100 == 0) {
                selectedList = rotateList(selectedList);
            }

            result = selectedList.isEmpty() ? null : selectedList.head();
        }

        return result;
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.proof.IGoalChooser#removeGoal(de.uka.ilkd.key.proof.Goal)
     *
     * The {@code GoalChooser} interface binds its goal type parameter to
     * {@code @Nullable ProofGoal} (generic-bound artifact), so it requires a
     * {@code @Nullable Goal} parameter here; the implementation only ever
     * receives non-null goals, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:override.param.invalid")
    public void removeGoal(Goal goal) {
        selectedList = selectedList.removeAll(goal);
        nextGoals = ImmutableList.nil();

        if (selectedList.isEmpty()) {
            setupGoals(goalList);
        }
    }


    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.proof.IGoalChooser#updateGoalList(de.uka.ilkd.key.proof.Node,
     * de.uka.ilkd.key.proof.IList<Goal>)
     *
     * The {@code GoalChooser} interface binds its goal type parameter to
     * {@code @Nullable ProofGoal} (generic-bound artifact), so it requires a
     * {@code @Nullable Goal} element here; the implementation only ever handles
     * non-null goals, suppressed with a scoped key. The proof is initialized while the goal
     * chooser is active; its dereference is suppressed with a scoped key.
     */
    @SuppressWarnings({ "nullness:override.param.invalid", "nullness:dereference.of.nullable" })
    public void updateGoalList(@Nullable Object node, @NonNull ImmutableList<Goal> newGoals) {
        if (newGoals.isEmpty() || (newGoals.tail().isEmpty() && newGoals.head().node() == node)) {
            // Goals (may) have been closed, remove them from the goal lists
            removeClosedGoals();
        } else {
            updateGoalListHelp(node, newGoals);
        }

        if (proof.openGoals().isEmpty())
        // proof has been closed
        {
            nextGoals = selectedList = goalList = ImmutableList.nil();
        } else {
            if (selectedList.isEmpty()
                    || (currentSubtreeRoot != null && !isSatisfiableSubtree(currentSubtreeRoot))) {
                setupGoals(goalList.prepend(selectedList));
            }
        }
    }

    protected void updateGoalListHelp(@Nullable Object node, ImmutableList<Goal> newGoals) {
        ImmutableList<Goal> prevGoalList = ImmutableList.nil();
        boolean newGoalsInserted = false;

        nextGoals = ImmutableList.nil();

        // Remove "node" and goals contained within "newGoals"
        while (!selectedList.isEmpty()) {
            final Goal goal = selectedList.head();
            selectedList = selectedList.tail();

            if (node == goal.node() || newGoals.contains(goal)) {
                // continue taclet apps at the next goal in list
                nextGoals = selectedList;

                if (!newGoalsInserted) {
                    prevGoalList = insertNewGoals(newGoals, prevGoalList);
                    newGoalsInserted = true;
                }
            } else {
                prevGoalList = prevGoalList.prepend(goal);
            }
        }

        while (!prevGoalList.isEmpty()) {
            selectedList = selectedList.prepend(prevGoalList.head());
            prevGoalList = prevGoalList.tail();
        }
    }

    /**
     * Inserts the given new goals into the goal list, keeping the list consistent with the open
     * goals of the proof.
     *
     * @param newGoals The new goals to insert.
     * @return The updated goal list.
     *         <p>
     *         The proof is initialized while the goal chooser is active; the dereference of the
     *         (nullable) proof field is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    protected ImmutableList<Goal> insertNewGoals(ImmutableList<Goal> newGoals,
            ImmutableList<Goal> prevGoalList) {

        for (final Goal g : newGoals) {
            if (proof.openGoals().contains(g)) {
                if (!allGoalsSatisfiable) {
                    goalList = goalList.prepend(g);
                } else {
                    prevGoalList = prevGoalList.prepend(g);
                }
            }
        }
        return prevGoalList;
    }


    protected static ImmutableList<Goal> rotateList(ImmutableList<Goal> p_list) {
        if (p_list.isEmpty()) {
            return ImmutableList.nil();
        }

        return p_list.tail().append(p_list.head());
    }

    /**
     * Removes the goal entries of closed goals from the goal list.
     * <p>
     * The proof is initialized while the goal chooser is active; the dereferences of the
     * (nullable) proof field are suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    protected void removeClosedGoals() {
        boolean changed = false;
        Iterator<Goal> it = goalList.iterator();
        goalList = ImmutableList.nil();

        while (it.hasNext()) {
            final Goal goal = it.next();
            if (proof.openGoals().contains(goal))
            // order of goals is not relevant
            {
                goalList = goalList.prepend(goal);
            }
        }

        it = selectedList.iterator();
        ImmutableList<Goal> newList = ImmutableList.nil();

        while (it.hasNext()) {
            final Goal goal = it.next();
            if (proof.openGoals().contains(goal)) {
                if (!allGoalsSatisfiable) {
                    goalList = goalList.prepend(goal);
                    changed = true;
                } else {
                    newList = newList.prepend(goal);
                }
            } else {
                changed = true;
            }
        }

        if (changed) {
            nextGoals = ImmutableList.nil();

            // for "selectedList", order does matter
            it = newList.iterator();
            selectedList = ImmutableList.nil();
            while (it.hasNext()) {
                selectedList = selectedList.prepend(it.next());
            }
        }
    }

    /**
     * Search for a minimal subtree of the proof tree which is not closable (constraints of its
     * goals are inconsistent) below p_startNode
     * <p>
     * PRECONDITION: * !isSatisfiableSubtree ( p_startNode ) * all goals have satisfiable
     * constraints
     * </p>
     *
     * @return true iff a non-empty subtree was found
     *         <p>
     *         The proof is initialized while the goal chooser is active; the dereference of the
     *         (nullable) proof field is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    protected boolean findMinimalSubtreeBelow(@NonNull Node p_startNode) {
        Node node = p_startNode;

        while (node.childrenCount() == 1) {
            node = node.child(0);
        }

        Iterator<Node> childrenIt = node.childrenIterator();

        while (childrenIt.hasNext()) {
            final Node child = childrenIt.next();

            if (isSatisfiableSubtree(child) && findMinimalSubtreeBelow(child)) {
                return true;
            }
        }

        currentSubtreeRoot = p_startNode;
        childrenIt = node.leavesIterator();

        while (childrenIt.hasNext()) {
            final Node child = childrenIt.next();
            final Goal goal = proof.getOpenGoal(child);

            // an inner node has no open goal: {@code contains(null)} can never match a goal list
            if (goal != null && goalList.contains(goal)) {
                selectedList = selectedList.prepend(goal);
                goalList = goalList.removeAll(goal);
            }
        }

        return !selectedList.isEmpty();

    }


    /**
     * Search for a minimal subtree of the proof tree which is not closable (constraints of its
     * goals are inconsistent) starting at p_startNode
     * <br/>
     * PRECONDITION: all goals have satisfiable constraints
     *
     * @param p_startNode the node from where to start the search
     *        <p>
     *        The proof is initialized while the goal chooser is active; the dereferences of the
     *        (nullable) proof field are suppressed with a scoped key. The walk {@code
     *        p_startNode = p_startNode.parent()} and the final root lookup are part of the same
     *        invariant: by the precondition the walk terminates at a satisfiable ancestor strictly
     *        below the proof root, so {@code parent()} never yields {@code null} on that path and
     *        the root of the active proof always exists; both differences are suppressed with
     *        scoped keys.
     */
    @SuppressWarnings({ "nullness:dereference.of.nullable",
        "nullness:assignment.type.incompatible", "nullness:argument.type.incompatible" })
    protected void findMinimalSubtree(@NonNull Node p_startNode) {
        while (!isSatisfiableSubtree(p_startNode)) {
            p_startNode = p_startNode.parent();
        }

        if (!findMinimalSubtreeBelow(p_startNode)) {
            findMinimalSubtreeBelow(proof.root());
        }
    }


    protected boolean isSatisfiableSubtree(@NonNull Node p_root) {
        return !p_root.isClosed();
    }

}
