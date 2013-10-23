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

package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabels;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;

/**
 * The {@link TermLabelInstantiator} used during prove to define how a
 * {@link LoopInvariantNormalBehaviorTermLabel} is maintained.
 * @author Martin Hentschel
 */
public final class LoopInvariantNormalBehaviorTermLabelInstantiator extends AbstractSymbolicExecutionInstantiator {
   /**
    * The only instance of this class.
    */
   public static final LoopInvariantNormalBehaviorTermLabelInstantiator INSTANCE = new LoopInvariantNormalBehaviorTermLabelInstantiator();

   /**
    * Constructor to forbid multiple instances.
    */
   private LoopInvariantNormalBehaviorTermLabelInstantiator() {
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean checkOperator(Operator newTermOp) {
      return Junctor.IMP == newTermOp;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected TermLabel getTermLabel(Term applicationTerm) {
      return TermLabels.LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL;
   }
}