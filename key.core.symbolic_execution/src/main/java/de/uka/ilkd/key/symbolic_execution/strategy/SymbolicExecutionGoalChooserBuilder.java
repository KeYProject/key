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

import de.uka.ilkd.key.prover.GoalChooserBuilder;
import de.uka.ilkd.key.prover.GoalChooser;

/**
 * This {@link GoalChooserBuilder} creates a special {@link GoalChooser}
 * for symbolic execution.
 * @author Martin Hentschel
 * @see SymbolicExecutionGoalChooser
 */
public class SymbolicExecutionGoalChooserBuilder implements GoalChooserBuilder {
   /**
    * The name of this goal chooser.
    */
   public static final String NAME = "Symbolic Execution Goal Chooser";

   /**
    * {@inheritDoc}
    */
   @Override
   public GoalChooser create() {
      return new SymbolicExecutionGoalChooser();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public GoalChooserBuilder copy() {
      return new SymbolicExecutionGoalChooserBuilder();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String name() {
      return NAME;
   }
}