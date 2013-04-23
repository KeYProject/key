package de.uka.ilkd.key.symbolic_execution.strategy;

import java.util.Vector;

import de.uka.ilkd.key.gui.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.gui.ApplyStrategy.SingleRuleApplicationInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

public class BreakpointStopCondition implements IStopCondition {

   private Vector<Integer> breakpointLineVector;
   
   public BreakpointStopCondition(Vector<Integer> breakpointLineVector){
      this.breakpointLineVector = breakpointLineVector;
   }
   
   @Override
   public int getMaximalWork(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser) {
      // TODO Auto-generated method stub
      return 0;
   }

   @Override
   public boolean isGoalAllowed(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser, long startTime, int countApplied, Goal goal) {
      // TODO Auto-generated method stub
      return true;
   }

   @Override
   public String getGoalNotAllowedMessage(int maxApplications, long timeout,
         Proof proof, IGoalChooser goalChooser, long startTime,
         int countApplied, Goal goal) {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public boolean shouldStop(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser, long startTime, int countApplied,
         SingleRuleApplicationInfo singleRuleApplicationInfo) {
      // TODO Auto-generated method stub
      if (singleRuleApplicationInfo != null) {  
   // Get the node on which a rule was applied.
      Goal goal = singleRuleApplicationInfo.getGoal();
      Node goalNode = goal.node();
     
      
      
      assert goalNode.childrenCount() == 0; // Make sure that this is the current goal node
      if(goalNode.parent().getNodeInfo().getActiveStatement()!=null&&goalNode.parent().getNodeInfo().getActiveStatement().getStartPosition().getLine()!=-1){
         int line = goalNode.parent().getNodeInfo().getActiveStatement().getStartPosition().getLine();
         return breakpointLineVector.contains(line);   
      }
      
      return false;}
      return false;
   }

   @Override
   public String getStopMessage(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser, long startTime, int countApplied,
         SingleRuleApplicationInfo singleRuleApplicationInfo) {
      // TODO Auto-generated method stub
      return null;
   }

}
