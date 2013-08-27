// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.strategy;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Services.ITermProgramVariableCollectorFactory;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.proof.TermProgramVariableCollectorKeepUpdatesForBreakpointconditions;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

public abstract class AbstractBreakpointStopCondition extends
      ExecutedSymbolicExecutionTreeNodesStopCondition {

   /**
    * The path of the class this {@link LineBreakpointStopCondition} is associated with.
    */
   private String classPath;
   
   /**
    * The flag if the Breakpoint is enabled.
    */
   protected boolean enabled;
   
   /**
    * The {@link IProgramMethod} this Breakpoint lies within
    */
   protected IProgramMethod pm;

   /**
    * The {@link KeYEnvironment} the proof is running in
    */
   protected KeYEnvironment<?> environment;

   /**
    * The {@link ITermProgramVariableCollectorFactory} for others to use when collecting variables to dismiss.
    */
   private ITermProgramVariableCollectorFactory programVariableCollectorFactory;
   
   /**
    * The {@link CompoundStopCondition} containing all BreakpointStopConditions relevant for the current {@link KeYEnvironment}
    */
   private CompoundStopCondition parentCondition;


   /**
    * Creates a new {@link AbstractBreakpointStopCondition}.
    * 
    * @param classPath the path of the class the associated Breakpoint lies within
    * @param environment the environment the that the proof that should be stopped is working in
    * @param pm the {@link IProgramMethod} representing the Method which the Breakpoint is located at
    * @param proof the {@link Proof} that will be executed and should stop
    * @param parentCondition a {@link CompoundStopCondition} containing this {@link LineBreakpointStopCondition} and all other {@link LineBreakpointStopCondition} the associated {@link Proof} should use
    * @param enabled flag if the Breakpoint is enabled
    */
   public AbstractBreakpointStopCondition(String classPath, KeYEnvironment<?> environment, IProgramMethod pm, Proof proof, CompoundStopCondition parentCondition, boolean enabled){
      super();
      this. environment = environment;
      this.pm = pm;
      this.classPath=classPath;
      this.enabled=enabled;
      this.parentCondition=parentCondition;
      createNewFactory();
      proof.getServices().setFactory(programVariableCollectorFactory);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isGoalAllowed(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser, long startTime, int countApplied, Goal goal) { 
         if(goal!=null){
            Node node = goal.node();
            RuleApp ruleApp = goal.getRuleAppManager().peekNext();
               if (SymbolicExecutionUtil.isSymbolicExecutionTreeNode(node, ruleApp)) {
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
                        getGoalAllowedResultPerSetNode().put(node, Boolean.FALSE);
                        return false; // Limit of set nodes of this goal exceeded
                     }
                     else {
                        SourceElement activeStatement = NodeInfo.computeActiveStatement(ruleApp);
                        if (activeStatement != null && activeStatement.getEndPosition().getLine() != -1) {
                           String path = activeStatement.getPositionInfo().getParentClass();
                           int line = activeStatement.getEndPosition().getLine();
                           try{
                              if(breakpointHit(line, path, ruleApp, proof, node)){
                                 // Increase number of set nodes on this goal and allow rule application
                                    executedNumberOfSetNodes = Integer.valueOf(executedNumberOfSetNodes.intValue() + 1);
                                    getExecutedNumberOfSetNodesPerGoal().put(goal, executedNumberOfSetNodes);
                                    getGoalAllowedResultPerSetNode().put(node, Boolean.TRUE);
                                 }
                           }catch(ProofInputException e){
                              //TODO
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

   
   /**
    * Determines whether the execution should stop with the given parameters
    * 
    * @param line the line of the currently executed statement
    * @param path the path of the class of the currently executed statement
    * @param ruleApp the applied ruleapp
    * @param proof the current proof
    * @param node the current node
    * @return true if execution should hold
    * @throws ProofInputException
    */
   protected boolean breakpointHit(int line, String path, RuleApp ruleApp, Proof proof, Node node)throws ProofInputException {
      return enabled;
   }

   /**
    * creates a new factory that should be used by others afterwards
    */
   private void createNewFactory() {
      programVariableCollectorFactory = new ITermProgramVariableCollectorFactory() {
         @Override
         public TermProgramVariableCollector create(Services services) {
            TermProgramVariableCollectorKeepUpdatesForBreakpointconditions collector = new TermProgramVariableCollectorKeepUpdatesForBreakpointconditions(services, parentCondition);
            
              return collector;
         }
      };
   }
   
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
    * Returns the path of the class the breakpoint is in.
    * @return the path of the class the breakpoint is in
    */
   public String getClassPath() {
      return classPath;
   }
}
