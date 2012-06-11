package de.uka.ilkd.key.symbolic_execution.strategy;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.proof.DepthFirstGoalChooser;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * <p>
 * This {@link IGoalChooser} is a special implementation of the default
 * {@link DepthFirstGoalChooser}. The difference is that a rule which
 * creates a new symbolic execution tree node on a {@link Goal} is only applied
 * if all other {@link Goal}s will also creates new symbolic execution tree
 * nodes. This has the advantage that invalid branches may closed before
 * new symbolic execution tree nodes are created.
 * </p>
 * <p>
 * The order in which new symbolic execution tree nodes are created is also
 * managed by this {@link IGoalChooser}. The idea is that on each {@link Goal}
 * is a new symbolic execution tree node created before on one {@link Goal}
 * is a second one created. This has the affect that for instance on all branches
 * of an if node the next statement is evaluated before the first branch 
 * executes the second statement.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicExecutionGoalChooserBuilder
 */
public class SymbolicExecutionGoalChooser extends DepthFirstGoalChooser {
   /**
    * This {@link Set} is used to count on which {@link Goal}s a 
    * symbolic execution node was executed. Initially it is filled in
    * {@link #getNextGoal()} with all possible {@link Goal}s. Every call
    * of {@link #getNextGoal()} will then remove a {@link Goal} from this list.
    * If a {@link Goal} is not contained in this list it is skipped in
    * {@link #getNextGoal()} until the {@link Set} is empty which indicates
    * that on all {@link Goal}s a symbolic execution tree node was created.
    * Then the process starts again.
    */
   private Set<Goal> goalsToPrefer = new HashSet<Goal>();
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Goal getNextGoal() {
      if (selectedList.size() >= 2) {
         Goal goal = null;
         // Reinitialize preferred set if required
         if (goalsToPrefer.isEmpty()) {
            for (Goal goalToPrefer: selectedList) {
               goalsToPrefer.add(goalToPrefer);
            }
         }
         // Select goal
         do {
            Goal next = super.getNextGoal();
            if (next == null) {
               return null;
            }
            Node node = next.node();
            RuleApp ruleApp = next.getRuleAppManager().peekNext();
            if (!SymbolicExecutionUtil.isSymbolicExecutionTreeNode(node, ruleApp)) {
               // Internal proof node, goal from super class can be used
               goal = next;
            }
            else {
               // Preferred goals should be used first, check if goal from super class is preferred
               if (goalsToPrefer.remove(next) || goalsToPrefer.isEmpty()) {
                  // Goal is preferred so return it as method result
                  goal = next;
               }
               // Check if a goal was found in this loop iteration, if not change order of goals in super class
               if (goal == null) {
                  // Update selected list to get a new goal in next loop iteration
                  Goal head = selectedList.head();
                  selectedList = selectedList.take(1);
                  selectedList = selectedList.append(head);
               }
            }
         } while (goal == null);
         return goal;
      }
      else {
         // Return the only goal
         return super.getNextGoal();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void init(Proof p_proof, ImmutableList<Goal> p_goals) {
      // Clear preferred set to make sure that it is refilled when the first Goal should be selected and no old state is used. 
      goalsToPrefer.clear();
      // Update available goals in super class
      super.init(p_proof, p_goals);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removeGoal(Goal p_goal) {
      // Update available goals in super class
      super.removeGoal(p_goal);
      // Remove no longer relevant goal from preferred set
      goalsToPrefer.remove(p_goal);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void updateGoalList(Node node, ImmutableList<Goal> newGoals) {
      // Temporary store old goals
      ImmutableList<Goal> oldGoals = selectedList;
      // Update available goals in super class
      super.updateGoalList(node, newGoals);
      // Remove no longer relevant goals from preferred set
      Iterator<Goal> preferredIter = goalsToPrefer.iterator();
      while (preferredIter.hasNext()) {
         Goal next = preferredIter.next();
         if (!proof.openGoals().contains(next)) {
            preferredIter.remove();
         }
      }
      // Add new goals to preferred set
      for (Goal goal : newGoals) {
         if (!oldGoals.contains(goal)) {
            goalsToPrefer.add(goal);
         }
      }
   }
}
