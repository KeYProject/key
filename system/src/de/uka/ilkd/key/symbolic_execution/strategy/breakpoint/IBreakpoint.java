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

package de.uka.ilkd.key.symbolic_execution.strategy.breakpoint;

import de.uka.ilkd.key.gui.configuration.StrategySettings;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Defines the basic functionality of a breakpoint.
 * @author Martin Hentschel
 */
public interface IBreakpoint {
   /**
    * Checks if the Breakpoint is enabled.
    * @return true if Breakpoint is enabled
    */
   public boolean isEnabled();
   
   /**
    * This method is called from 
    * {@link IStopCondition#isGoalAllowed(int, long, Proof, IGoalChooser, long, int, Goal)}
    * and can be used to update the state of the {@link IBreakpoint}.
    * @param maxApplications The defined maximal number of rules to apply. Can be different to {@link StrategySettings#getMaxSteps()} in side proofs.
    * @param timeout The defined timeout in ms or {@code -1} if disabled. Can be different to {@link StrategySettings#getTimeout()} in side proofs.
    * @param proof The current {@link Proof}.
    * @param goalChooser The current {@link IGoalChooser}.
    * @param startTime The timestamp when the apply strategy has started, computed via {@link System#currentTimeMillis()}
    * @param countApplied The number of already applied rules.
    * @param goal The current {@link Goal} on which the next rule will be applied.
    */
   public void updateState(int maxApplications, 
                           long timeout, 
                           Proof proof, 
                           IGoalChooser goalChooser, 
                           long startTime, 
                           int countApplied, 
                           Goal goal);
   
   /**
    * Determines if the breakpoint represented by this BreakpointStopConition is triggered.
    * Override this method in order to suspend execution when a breakpoint is hit.
    * @param activeStatement the activeStatement of the node
    * @param ruleApp the applied {@link RuleApp}
    * @param proof the current proof
    * @param node the current node
    * @return true if execution should hold
    */
   public boolean isBreakpointHit(SourceElement activeStatement, 
                                  RuleApp ruleApp, 
                                  Proof proof, 
                                  Node node);
}