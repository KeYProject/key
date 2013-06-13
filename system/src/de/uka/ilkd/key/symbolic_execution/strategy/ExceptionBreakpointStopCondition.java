package de.uka.ilkd.key.symbolic_execution.strategy;

import java.util.Iterator;

import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.ApplyStrategy.SingleRuleApplicationInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Node.NodeIterator;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessBranchNode;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.Pair;

public class ExceptionBreakpointStopCondition extends
      ExecutedSymbolicExecutionTreeNodesStopCondition {
   
   private IProgramVariable exceptionVariable;
   private SymbolicExecutionEnvironment<?> env;
   private String exceptionName;
   private boolean exceptionThrown;

   public ExceptionBreakpointStopCondition(SymbolicExecutionEnvironment<?>env, String exceptionName){
      this.exceptionVariable = SymbolicExecutionUtil.extractExceptionVariable(env.getBuilder().getProof());
      this.env = env;
      this.exceptionName = exceptionName;
      exceptionThrown = false;
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
         
            // Check if the result for the current node was already computed.
            Boolean value = getGoalAllowedResultPerSetNode().get(node);
            if (value == null) {
               // Get the number of executed set nodes on the current goal
               Integer executedNumberOfSetNodes = getExecutedNumberOfSetNodesPerGoal().get(goal);
               if (executedNumberOfSetNodes == null) {
                  executedNumberOfSetNodes = Integer.valueOf(0);
               }
               // Check if limit of set nodes of the current goal is exceeded
               if (executedNumberOfSetNodes.intValue() + 1 > getMaximalNumberOfSetNodesToExecutePerGoal()) {
                  Node parent = SymbolicExecutionUtil.findParentSetNode(node);
                  System.out.println("Stopped for  Exception at : "+node.serialNr()+" with parent: "+ parent.serialNr());
                  getGoalAllowedResultPerSetNode().put(node, Boolean.FALSE);
                  return false;
                   // Limit of set nodes of this goal exceeded
               }
               else {
                  SourceElement activeStatement = NodeInfo.computeActiveStatement(ruleApp);
                  if(activeStatement!=null&&activeStatement.toString().equals("throw new "+exceptionName+" ();")){
                     Node parent = SymbolicExecutionUtil.findParentSetNode(node);
                     System.out.println("Found Exception at : "+node.serialNr()+" with parent: "+ parent.serialNr());
                     executedNumberOfSetNodes = Integer.valueOf(executedNumberOfSetNodes.intValue() + 1);
                     getExecutedNumberOfSetNodesPerGoal().put(goal, executedNumberOfSetNodes);
                     getGoalAllowedResultPerSetNode().put(node, Boolean.TRUE);
                  }
               }
            }
            else {
               // Reuse already computed result.
               System.out.println("Reuse: "+value.booleanValue()+"From :"+node.serialNr());
               return value.booleanValue();
            }
         
      }
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
      // Check if a rule was applied
      if (singleRuleApplicationInfo != null) {
         // Get the node on which a rule was applied.
         Goal goal = singleRuleApplicationInfo.getGoal();
         Node goalNode = goal.node();
         assert goalNode.childrenCount() == 0; // Make sure that this is the current goal node
         Node updatedNode = goalNode.parent();
         // Check if multiple branches where created.
         if (updatedNode.childrenCount() >= 2) {
            // If a number of executed set nodes is available for the goal it must be used for all other new created goals.
            Integer executedValue = getExecutedNumberOfSetNodesPerGoal().get(goal);
            if (executedValue != null) {
               // Reuse number of set nodes for new created goals
               NodeIterator childIter = updatedNode.childrenIterator();
               while (childIter.hasNext()) {
                  Node next = childIter.next();
                  Goal nextGoal = next.proof().getGoal(next);
                  // Check if the current goal is a new one
                  if (nextGoal != goal) {
                     // New goal found, use the number of set nodes for it.
                     getExecutedNumberOfSetNodesPerGoal().put(nextGoal, executedValue);
                  }
               }
            }
         }
      }
      return false;
   }
   
   
//   /**
//    * {@inheritDoc}
//    */
//   @Override
//   public boolean shouldStop(int maxApplications, 
//                             long timeout, 
//                             Proof proof, 
//                             IGoalChooser goalChooser, 
//                             long startTime, 
//                             int countApplied, 
//                             SingleRuleApplicationInfo singleRuleApplicationInfo) {
//      // Check if a rule was applied
//      if (singleRuleApplicationInfo != null) {
//         // Get the node on which a rule was applied.
//         Goal goal = singleRuleApplicationInfo.getGoal();
//         Node goalNode = goal.node();
//         assert goalNode.childrenCount() == 0; // Make sure that this is the current goal node
//         SourceElement activeStatement = NodeInfo.computeActiveStatement(singleRuleApplicationInfo.getAppliedRuleApp());
//         if(activeStatement!=null&&activeStatement.toString().equals("throw new "+exceptionName+" ();")){
//            System.out.println(activeStatement+" "+ goalNode.serialNr());
//            return true;
//         }
//      }
//      return false;
//   }
   
   /**
    * Computes the exception {@link Sort} lazily when {@link #getExceptionSort()}
    * is called the first time. 
    * @return The exception {@link Sort}.
    */
   private Sort lazyComputeExceptionSort(Node node) {
      Sort result = null;
      if (exceptionVariable != null) {
         // Search final value of the exceptional variable which is used to check if the verified program terminates normally
         ImmutableArray<Term> value = null;
         for (SequentFormula f : node.sequent().succedent()) {
            Pair<ImmutableList<Term>,Term> updates = TermBuilder.DF.goBelowUpdates2(f.formula());
            Iterator<Term> iter = updates.first.iterator();
            while (value == null && iter.hasNext()) {
               value = extractValueFromUpdate(iter.next(), exceptionVariable);
            }
         }
         // An exceptional termination is found if the exceptional variable is not null
         if (value != null && value.size() == 1) {
            result = value.get(0).sort();
         }
      }
      return result;
   }
   
   /**
    * Utility method to extract the value of the {@link IProgramVariable}
    * from the given update term.
    * @param term The given update term.
    * @param variable The {@link IProgramVariable} for that the value is needed.
    * @return The found value or {@code null} if it is not defined in the given update term.
    */
   private ImmutableArray<Term> extractValueFromUpdate(Term term,
                                                         IProgramVariable variable) {
      ImmutableArray<Term> result = null;
      if (term.op() instanceof ElementaryUpdate) {
         ElementaryUpdate update = (ElementaryUpdate)term.op();
         if (JavaUtil.equals(variable, update.lhs())) {
            result = term.subs();
         }
      }
      else if (term.op() instanceof UpdateJunctor) {
         Iterator<Term> iter = term.subs().iterator();
         while (result == null && iter.hasNext()) {
            result = extractValueFromUpdate(iter.next(), variable);
         }
      }
      return result;
   }
}
