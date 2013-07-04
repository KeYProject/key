package de.uka.ilkd.key.symbolic_execution.strategy;

import java.util.HashSet;
import java.util.Set;

import org.eclipse.core.runtime.CoreException;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.ApplyStrategy.SingleRuleApplicationInfo;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.Throw;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

public class ExceptionBreakpointStopCondition extends
      ExecutedSymbolicExecutionTreeNodesStopCondition {
   private SymbolicExecutionEnvironment<?> env;
   private String exceptionName;
   private Set<Node> exceptionNodes;
   private Set<Node> exceptionParentNodes;
   private boolean caught;
   private boolean suspendOnSubclasses;
   private boolean uncaught;
   private boolean enabled;
   
   
   /**
    * The HitCount of the Breakpoint (set by user).
    */
   private int hitCount;
   
   /**
    * Counter for how often the Breakpoint was hit.
    */
   private int hitted = 0;

   public ExceptionBreakpointStopCondition(SymbolicExecutionEnvironment<?>env, String exceptionName, boolean caught, boolean uncaught, boolean suspendOnSubclasses, boolean enabled, int hitCount){
      this.env = env;
      this.exceptionName = exceptionName;
      exceptionNodes = new HashSet<Node>();
      exceptionParentNodes = new HashSet<Node>();
      this.enabled=enabled;
      this.caught=caught;
      this.uncaught=uncaught;
      this.suspendOnSubclasses=suspendOnSubclasses;
      this.hitCount = hitCount;
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
      if (goal != null) {
         Node node = goal.node();
         // Check if goal is allowed
         RuleApp ruleApp = goal.getRuleAppManager().peekNext();
         SourceElement activeStatement = NodeInfo.computeActiveStatement(ruleApp);
         Node SETParent = SymbolicExecutionUtil.findParentSetNode(node);
         if(activeStatement!=null&&activeStatement instanceof Throw&&enabled){
            Throw throwStatement = (Throw)activeStatement;
            for(int i = 0; i<throwStatement.getChildCount();i++){
               SourceElement childElement = throwStatement.getChildAt(i);
               if(childElement instanceof LocationVariable){
                  LocationVariable locVar = (LocationVariable)childElement;
                  if(locVar.getKeYJavaType().getSort().toString().equals(exceptionName)&&!exceptionParentNodes.contains(SETParent)){
                     exceptionNodes.add(node);
                     exceptionParentNodes.add(SETParent);
                  }else if(suspendOnSubclasses){
                     JavaInfo info = env.getServices().getJavaInfo();
                     KeYJavaType kjt = locVar.getKeYJavaType();
                     ImmutableList<KeYJavaType> kjts = info.getAllSupertypes(kjt);
                     for(KeYJavaType kjtloc: kjts){
                        if(kjtloc.getSort().toString().equals(exceptionName)&&!exceptionParentNodes.contains(SETParent)){
                           exceptionNodes.add(node);
                           exceptionParentNodes.add(SETParent);
                        }
                     }
                  }
               }
            }
         }
      }
      return true;
   }


   
   /**
    * Checks if the given node is a parent of the other given node.
    * @param node The {@link Node} to start search in.
    * @param node The {@link Node} that is thought to be the parent.
    * @return true if the parent node is one of the nodes parents
    */
   public static boolean isParentNode(Node node, Node parent) {
      if (node != null) {
         Node parentIter = node.parent();
         boolean result = false;
         while (parentIter != null && !result) {
            if (parentIter.equals(parent)) {
               result = true;
            }
            else {
               parentIter = parentIter.parent();
            }
         }
         return result;
      }
      else {
         return false;
      }
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
   // Check if a rule was applied
      if (singleRuleApplicationInfo != null) {
         // Get the node on which a rule was applied.
         Goal goal = singleRuleApplicationInfo.getGoal();
         Node node = goal.node();
         RuleApp ruleApp = goal.getRuleAppManager().peekNext();
         Node parent = null;
         for(Node parents : exceptionNodes){
            if(isParentNode(node, parents)){
               parent = parents;
            }
         }
         if(parent!=null
               && SymbolicExecutionUtil.isSymbolicExecutionTreeNode(node, ruleApp)
               &&!exceptionParentNodes.isEmpty()){
            if(SymbolicExecutionUtil.isTerminationNode(node, ruleApp)&&uncaught){
               if(hitcountExceeded()){
                  exceptionNodes.remove(parent);
                  return true;
               }
            } 
            else if(!SymbolicExecutionUtil.isTerminationNode(node, ruleApp)&&caught){
               if(hitcountExceeded()){
                  exceptionNodes.remove(parent);
                  return true;
               }
            }
            exceptionNodes.remove(parent);
         }

      }
      
      return false;
   }

   /**
    * Checks if the Hitcount is exceeded for the given {@link JavaLineBreakpoint}.
    * If the Hitcount is not exceeded the hitted counter is incremented, otherwise its set to 0.
    * 
    * @return true if the Hitcount is exceeded or the {@link JavaLineBreakpoint} has no Hitcount.
    * @throws CoreException
    */
   private boolean hitcountExceeded(){
      if (!(hitCount == -1)) {
         if (hitCount == hitted + 1) {
            hitted=0;
            return true;
         }
         else {
           hitted++;
         }
      }
      else {
         return true;
      }
      return false;
   }
   
   /**
    * @return the isCaught
    */
   public boolean isCaught() {
      return caught;
   }
   /**
    * @param isCaught the isCaught to set
    */
   public void setCaught(boolean isCaught) {
      this.caught = isCaught;
   }
   /**
    * @return the isUncaught
    */
   public boolean isUncaught() {
      return uncaught;
   }
   /**
    * @param isUncaught the isUncaught to set
    */
   public void setUncaught(boolean isUncaught) {
      this.uncaught = isUncaught;
   }
   /**
    * @return the isEnabled
    */
   public boolean isEnabled() {
      return enabled;
   }
   /**
    * @param isEnabled the isEnabled to set
    */
   public void setEnabled(boolean isEnabled) {
      this.enabled = isEnabled;
   }
   

   /**
    * Returns the hitCount of the associated Breakpoint.
    * @return the hitCount of the associated Breakpoint
    */
   public int getHitCount() {
      return hitCount;
   }
   
   /**
    * Set the hitCount to the new value
    * @param hitCount the new value
    */
   public void setHitCount(int hitCount) {
      this.hitCount = hitCount;
   }
   
   /**
    * @return the suspendOnSubclasses
    */
   public boolean isSuspendOnSubclasses() {
      return suspendOnSubclasses;
   }
   /**
    * @param suspendOnSubclasses the suspendOnSubclasses to set
    */
   public void setSuspendOnSubclasses(boolean suspendOnSubclasses) {
      this.suspendOnSubclasses = suspendOnSubclasses;
   }
}
