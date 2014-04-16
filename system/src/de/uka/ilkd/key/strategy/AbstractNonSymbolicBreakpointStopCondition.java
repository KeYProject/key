package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.gui.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.gui.ApplyStrategy.SingleRuleApplicationInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.RuleApp;

public abstract class AbstractNonSymbolicBreakpointStopCondition implements IStopCondition {
   /**
    * The flag if the Breakpoint is enabled.
    */
   private boolean enabled;
   
   /**
    * The proof this stop condition is associated with.
    */
   private final Proof proof; 
   
   /**
    * Constructor.
    * @param proof The proof this stop condition is associated with.
    * @param enabled The flag if the Breakpoint is enabled.
    */
   public AbstractNonSymbolicBreakpointStopCondition(Proof proof, boolean enabled) {
      this.proof = proof;
      this.enabled = enabled;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isGoalAllowed(int maxApplications, 
                                long timeout, 
                                Proof proof, 
                                IGoalChooser goalChooser, 
                                long startTime, 
                                int countApplied, 
                                Goal goal) {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean shouldStop(int maxApplications, 
                             long timeout, 
                             Proof proof, 
                             IGoalChooser goalChooser, 
                             long startTime, 
                             int countApplied, 
                             SingleRuleApplicationInfo singleRuleApplicationInfo) { 
      try {
         if (singleRuleApplicationInfo != null) {
            Goal goal = singleRuleApplicationInfo.getGoal();
            Node node = goal.node();
            RuleApp ruleApp = singleRuleApplicationInfo.getAppliedRuleApp();
            SourceElement activeStatement = NodeInfo.computeActiveStatement(ruleApp);
            if(isBreakpointHit(activeStatement, ruleApp, proof, node)){
               return true;
            }
         }
      }
      catch(ProofInputException e){
      }
      return false;
   }
   
   /**
    * Determines if the breakpoint represented by this BreakpointStopConition is triggered.
    * Override this method in order to suspend execution when a breakpoint is hit.
    * 
    * @param activeStatement the activeStatement of the node
    * @param ruleApp the applied ruleapp
    * @param proof the current proof
    * @param node the current node
    * @return true if execution should hold
    * @throws ProofInputException
    */
   protected abstract boolean isBreakpointHit(SourceElement activeStatement, 
                                              RuleApp ruleApp, 
                                              Proof proof, 
                                              Node node) throws ProofInputException;
   
   /**
    * Checks if the Breakpoint is enabled.
    * @return true if Breakpoint is enabled
    */
   public boolean isEnabled() {
      return enabled;
   }

   /**
    * Sets the new enabled value.
    * @param enabled the new value
    */
   public void setEnabled(boolean enabled) {
      this.enabled = enabled;
   }

   /**
    * @return the proof
    */
   public Proof getProof() {
      return proof;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getMaximalWork(int maxApplications, 
                             long timeout, 
                             Proof proof, 
                             IGoalChooser goalChooser) {
      return 0;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getGoalNotAllowedMessage(int maxApplications, 
                                          long timeout, 
                                          Proof proof, 
                                          IGoalChooser goalChooser, 
                                          long startTime, 
                                          int countApplied, 
                                          Goal goal) {
      return "Breakpoint hit!";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getStopMessage(int maxApplications, 
                                long timeout, 
                                Proof proof, 
                                IGoalChooser goalChooser, 
                                long startTime, 
                                int countApplied, 
                                SingleRuleApplicationInfo singleRuleApplicationInfo) {
      return "Breakpoint hit!";
   }
}
