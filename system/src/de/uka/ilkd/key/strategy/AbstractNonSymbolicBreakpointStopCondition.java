package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.gui.ApplyStrategy.SingleRuleApplicationInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.strategy.BreakpointStopCondition;

public abstract class AbstractNonSymbolicBreakpointStopCondition extends BreakpointStopCondition {

   public AbstractNonSymbolicBreakpointStopCondition(Proof proof, boolean enabled) {
      super(proof, enabled);
   }

   @Override
   public boolean isGoalAllowed(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser, long startTime, int countApplied, Goal goal) {
      // TODO Auto-generated method stub
      return true;
   }

   @Override
   public boolean shouldStop(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser, long startTime, int countApplied,
         SingleRuleApplicationInfo singleRuleApplicationInfo) { 
      try{
         if (singleRuleApplicationInfo != null) {
            Goal goal = singleRuleApplicationInfo.getGoal();
            Node node = goal.node();
            RuleApp ruleApp = singleRuleApplicationInfo.getAppliedRuleApp();
            SourceElement activeStatement = NodeInfo.computeActiveStatement(ruleApp);
               if(isBreakpointHit(activeStatement, ruleApp, proof, node)){
                  return true;
               }
         }
      }catch(ProofInputException e){
         //TODO
      }
      return false;
   }

}
