package org.key_project.keyide.ui.test.util;

import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.gui.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.gui.ApplyStrategy.SingleRuleApplicationInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Proof;

// TODO: Delete me, I think is not required
public class BlockingStopCondition implements IStopCondition {
   
   private boolean blockExecution;

   @Override
   public int getMaximalWork(int maxApplications, long timeout, Proof proof, IGoalChooser goalChooser) {
      return 0;
   }

   @Override
   public boolean isGoalAllowed(int maxApplications, long timeout, Proof proof, IGoalChooser goalChooser, long startTime, int countApplied, Goal goal) {
      return true; // Allow rule application.
   }

   @Override
   public String getGoalNotAllowedMessage(int maxApplications, long timeout, Proof proof, IGoalChooser goalChooser, long startTime, int countApplied, Goal goal) {
      return null;
   }

   @Override
   public boolean shouldStop(int maxApplications, long timeout, Proof proof, IGoalChooser goalChooser, long startTime, int countApplied, SingleRuleApplicationInfo singleRuleApplicationInfo) {
      while (blockExecution) {
         TestUtilsUtil.sleep(100); // Don't waste CPU time
      }
      return false; // Let the strategy decide when to stop
   }

   @Override
   public String getStopMessage(int maxApplications, long timeout, Proof proof, IGoalChooser goalChooser, long startTime, int countApplied, SingleRuleApplicationInfo singleRuleApplicationInfo) {
      return null;
   }

   public boolean isBlockExecution() {
      return blockExecution;
   }

   public void setBlockExecution(boolean blockExecution) {
      this.blockExecution = blockExecution;
   }
}
