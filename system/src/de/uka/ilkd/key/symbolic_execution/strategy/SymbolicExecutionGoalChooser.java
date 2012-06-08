package de.uka.ilkd.key.symbolic_execution.strategy;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.proof.DepthFirstGoalChooser;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * This {@link IGoalChooser} is a special implementation of the default
 * {@link DepthFirstGoalChooser}. The difference is that a rule which
 * creates a new symbolic execution tree node on {@link Goal} is only applied
 * if all other {@link Goal}s will also creates new symbolic execution tree
 * nodes. This has the advantage that invalid branches may closed before
 * new symbolic execution tree nodes are created.
 * @author Martin Hentschel
 * @see SymbolicExecutionGoalChooserBuilder
 */
public class SymbolicExecutionGoalChooser extends DepthFirstGoalChooser {
   /**
    * {@inheritDoc}
    */
   @Override
   public Goal getNextGoal() {
      if (selectedList.size() >= 2) {
         Goal goal = null;
         Set<Goal> checkedGoals = new HashSet<Goal>();
         do {
            Goal next = super.getNextGoal();
            if (next == null) {
               return null;
            }
            Node node = next.node();
            RuleApp ruleApp = next.getRuleAppManager().peekNext();
            if (!SymbolicExecutionUtil.isSymbolicExecutionTreeNode(node, ruleApp)) {
               goal = next;
            }
            else {
               if (!checkedGoals.add(next)) {
                  goal = next;
               }
               else {
                  Goal head = selectedList.head();
                  selectedList = selectedList.take(1);
                  selectedList = selectedList.append(head);
               }
            }
         } while (goal == null);
         return goal;
      }
      else {
         return super.getNextGoal();
      }
   }
}
