// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.strategy;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.IBreakpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint;

/**
 * An {@link IBreakpointStopCondition} which can be used during symbolic execution.
 * @author Martin Hentschel
 */
public class SymbolicExecutionBreakpointStopCondition extends ExecutedSymbolicExecutionTreeNodesStopCondition implements IBreakpointStopCondition {
   /**
    * The used {@link IBreakpoint}s.
    */
   private final Set<IBreakpoint> breakpoints = new HashSet<IBreakpoint>();

   /**
    * Creates a new {@link SymbolicExecutionBreakpointStopCondition}.
    * @param breakpoints The {@link IBreakpoint} to use.
    */
   public SymbolicExecutionBreakpointStopCondition(IBreakpoint... breakpoints) {
      super(Integer.MAX_VALUE);
      if (breakpoints != null) {
         for (IBreakpoint breakpoint : breakpoints) {
            this.breakpoints.add(breakpoint);
         }
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public int getMaximalWork(int maxApplications, 
                             long timeout, 
                             Proof proof, 
                             IGoalChooser goalChooser) {
      setMaximalNumberOfSetNodesToExecutePerGoal(Integer.MAX_VALUE);
      return super.getMaximalWork(maxApplications, timeout, proof, goalChooser);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isGoalAllowed(int maxApplications, long timeout, Proof proof, IGoalChooser goalChooser, long startTime, int countApplied, Goal goal) {
      for (IBreakpoint breakpoint : breakpoints) {
         breakpoint.updateState(maxApplications, timeout, proof, goalChooser, startTime, countApplied, goal);
      }
      return super.isGoalAllowed(maxApplications, timeout, proof, goalChooser, startTime, countApplied, goal);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleNodeLimitNotExceeded(int maxApplications, 
                                             long timeout, 
                                             Proof proof, 
                                             IGoalChooser goalChooser, 
                                             long startTime, 
                                             int countApplied, 
                                             Goal goal,
                                             Node node,
                                             RuleApp ruleApp,
                                             Integer executedNumberOfSetNodes) {
      super.handleNodeLimitNotExceeded(maxApplications, timeout, proof, goalChooser, startTime, countApplied, goal, node, ruleApp, executedNumberOfSetNodes);
      SourceElement activeStatement = NodeInfo.computeActiveStatement(ruleApp);
      if (isBreakpointHit(activeStatement, ruleApp, proof, node)) {
         setMaximalNumberOfSetNodesToExecutePerGoal(executedNumberOfSetNodes.intValue());
      }
   }
   
   /**
    * Checks if a breakpoint is hit.
    * @param activeStatement the activeStatement of the node
    * @param ruleApp the applied {@link RuleApp}
    * @param proof the current proof
    * @param node the current node
    * @return {@code true} at least one breakpoint is hit, {@code false} all breakpoints are not hit.
    */
   protected boolean isBreakpointHit(SourceElement activeStatement, RuleApp ruleApp, Proof proof, Node node) {
      boolean result = false;
      Iterator<IBreakpoint> iter = breakpoints.iterator();
      while (!result && iter.hasNext()) {
         IBreakpoint next = iter.next();
         result = next.isEnabled() && next.isBreakpointHit(activeStatement, ruleApp, proof, node);
      }
      return result;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void addBreakpoint(IBreakpoint breakpoint) {
      breakpoints.add(breakpoint);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void removeBreakpoint(IBreakpoint breakpoint) {
      breakpoints.remove(breakpoint);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Set<IBreakpoint> getBreakpoints() {
      return breakpoints;
   }
}