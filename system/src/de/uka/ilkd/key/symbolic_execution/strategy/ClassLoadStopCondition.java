package de.uka.ilkd.key.symbolic_execution.strategy;

import org.eclipse.core.runtime.CoreException;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.VariableDeclaration;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

public class ClassLoadStopCondition extends
      ExecutedSymbolicExecutionTreeNodesStopCondition {

   

   private KeYEnvironment<?> environment;

   private boolean enabled;
   
   private boolean wasLoaded;

   private KeYJavaType containerKJT;

   private String fullFieldName;
   
   /**
    * The HitCount of the Breakpoint (set by user).
    */
   private int hitCount;
   
   /**
    * Counter for how often the Breakpoint was hit.
    */
   private int hitted = 0;
   
   public ClassLoadStopCondition(KeYEnvironment<?> environment,
         boolean enabled, KeYJavaType containerKJT, int hitCount) {
      super();
      this.environment = environment;
      this.enabled = enabled;
      this.containerKJT = containerKJT;
      this.hitCount = hitCount;
      this.wasLoaded = false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isGoalAllowed(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser, long startTime, int countApplied, Goal goal) {
      if (goal != null) {
         Node node = goal.node();
         RuleApp ruleApp = goal.getRuleAppManager().peekNext();
         
         if (SymbolicExecutionUtil.isSymbolicExecutionTreeNode(node, ruleApp)) {
            // Check if the result for the current node was already computed.
            Boolean value = getGoalAllowedResultPerSetNode().get(node);
            if (value == null) {
               // Get the number of executed set nodes on the current goal
               Integer executedNumberOfSetNodes = getExecutedNumberOfSetNodesPerGoal()
                     .get(goal);
               if (executedNumberOfSetNodes == null) {
                  executedNumberOfSetNodes = Integer.valueOf(0);
               }
               // Check if limit of set nodes of the current goal is exceeded
               if (executedNumberOfSetNodes.intValue() + 1 > getMaximalNumberOfSetNodesToExecutePerGoal()) {
                  getGoalAllowedResultPerSetNode().put(node, Boolean.FALSE);
                  return false; // Limit of set nodes of this goal exceeded
               }
               else {
                     if (enabled) {
                        SourceElement activeStatement = NodeInfo.computeActiveStatement(ruleApp);
                        if (activeStatement != null) {
                           if(isClassLoadStatement(activeStatement, ruleApp)&&hitcountExceeded()){
                              // Increase number of set nodes on this goal and allow rule application
                              executedNumberOfSetNodes = Integer.valueOf(executedNumberOfSetNodes.intValue() + 1);
                              getExecutedNumberOfSetNodesPerGoal().put(goal, executedNumberOfSetNodes);
                              getGoalAllowedResultPerSetNode().put(node, Boolean.TRUE);
                           }
                        }
                     }
                  return true;
               }
            }
            else {
               // Reuse already computed result.
               return value.booleanValue();
            }
         }

      }
      return true;
   }
   private boolean isClassLoadStatement(SourceElement activeStatement, RuleApp ruleApp) {
      if(activeStatement instanceof MethodBodyStatement&&!wasLoaded){
         MethodBodyStatement mbs = (MethodBodyStatement)activeStatement;
         JavaInfo info = environment.getServices().getJavaInfo();
         ImmutableList<KeYJavaType> kjts = info.getAllSupertypes(mbs.getBodySource());
         for(KeYJavaType kjtloc: kjts){
            if(kjtloc.equals(containerKJT)){
              wasLoaded = true;
              return true;
            }
         }
      }
      else if(activeStatement instanceof Assignment&&!wasLoaded){
         Assignment assignment = (Assignment) activeStatement;
         SourceElement firstElement = assignment.getFirstElement();
         if(firstElement instanceof LocationVariable){
            LocationVariable locVar = (LocationVariable) firstElement;
            JavaInfo info = environment.getServices().getJavaInfo();
            ImmutableList<KeYJavaType> kjts = info.getAllSupertypes(locVar.getContainerType());
            for(KeYJavaType kjtloc: kjts){
               if(kjtloc.equals(containerKJT)){
                 wasLoaded = true;
                 return true;
               }
            }
         }
         for(int i = 1; i<assignment.getChildCount();i++){
            SourceElement childElement = assignment.getChildAt(i);
            if(childElement instanceof FieldReference){
               FieldReference field = (FieldReference)childElement;
               JavaInfo info = environment.getServices().getJavaInfo();
               ImmutableList<KeYJavaType> kjts = info.getAllSupertypes(field.getProgramVariable().getContainerType());
               for(KeYJavaType kjtloc: kjts){
                  if(kjtloc.equals(containerKJT)){
                    wasLoaded = true;
                    return true;
                  }
               }
            }else if (childElement instanceof MethodReference) {
               return isClassLoadStatement(childElement, ruleApp);
            }
         }
      }
      else if(activeStatement instanceof MethodReference&&!wasLoaded){
         System.out.println("methodreference");
//         MethodReference methodReference = (MethodReference)activeStatement;
//         JavaInfo info = environment.getServices().getJavaInfo();
//         PosInOccurrence pio = ruleApp.posInOccurrence();
//         Term term = pio.subTerm();
//         term = TermBuilder.DF.goBelowUpdates(term);
//         ExecutionContext ec = JavaTools.getInnermostExecutionContext(term.javaBlock(), environment.getServices());
//         System.out.println(methodReference.getKeYJavaType(environment.getServices(), ec));
//         ImmutableList<KeYJavaType> kjts = info.getAllSupertypes(mbs.getBodySource());
//         for(KeYJavaType kjtloc: kjts){
//            if(kjtloc.equals(containerKJT)){
//              wasLoaded = true;
//              return true;
//            }
//         }
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

   public int getHitCount() {
      return hitCount;
   }

   public void setHitCount(int hitCount) {
      this.hitCount = hitCount;
   }


   public boolean isEnabled() {
      return enabled;
   }

   public void setEnabled(boolean enabled) {
      this.enabled = enabled;
   }

}
