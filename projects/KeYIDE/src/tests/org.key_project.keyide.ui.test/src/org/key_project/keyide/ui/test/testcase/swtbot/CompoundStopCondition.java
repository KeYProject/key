package org.key_project.keyide.ui.test.testcase.swtbot;

import de.uka.ilkd.key.gui.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.gui.ApplyStrategy.SingleRuleApplicationInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Proof;

public class CompoundStopCondition implements IStopCondition{

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
      return false;
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
