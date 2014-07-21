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

import de.uka.ilkd.key.gui.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Proof;

/**
 * This {@link IStopCondition} stops the auto mode when a "step over" is completed.
 * This is the case when the next symbolic execution tree node was executed on a {@link Goal} 
 * which has the same call or lower stack size as the symbolic execution tree node of the {@link Goal} 
 * on which the auto mode was started.
 * @author Martin Hentschel
 */
public class StepOverSymbolicExecutionTreeNodesStopCondition extends AbstractCallStackBasedStopCondition {   
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean isCallStackSizeReached(int initialCallStackSize, int currentCallStackSize) {
      return currentCallStackSize <= initialCallStackSize;
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
      return "Step over completed.";
   }
}