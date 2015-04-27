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

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Proof;

/**
 * Provides the basic implementation of an {@link IBreakpoint}.
 * @author Martin Hentschel
 */
public abstract class AbstractBreakpoint implements IBreakpoint {
   /**
    * The proof this stop condition is associated with.
    */
   private final Proof proof;

   /**
    * The flag if the Breakpoint is enabled.
    */
   private boolean enabled;
   
   /**
    * Constructor.
    * @param proof The {@link Proof} in which this {@link IBreakpoint} is used.
    * @param enabled The enabled state.
    */
   public AbstractBreakpoint(Proof proof, boolean enabled) {
      this.proof = proof;
      this.enabled = enabled;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void updateState(int maxApplications, 
                          long timeout, 
                          Proof proof, 
                          IGoalChooser goalChooser, 
                          long startTime, 
                          int countApplied, 
                          Goal goal) {
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
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
}