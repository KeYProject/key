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

import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.label.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.AbstractSymbolicExecutionInstantiator;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * The {@link ITermLabelWorker} used during prove to define how a
 * {@link SymbolicExecutionTermLabel} is maintained.
 * @author Martin Hentschel
 */
public final class SymbolicExecutionTermLabelInstantiator extends AbstractSymbolicExecutionInstantiator {
   /**
    * The only instance of this class.
    */
   public static final SymbolicExecutionTermLabelInstantiator INSTANCE = new SymbolicExecutionTermLabelInstantiator();

   /**
    * Constructor to forbid multiple instances.
    */
   private SymbolicExecutionTermLabelInstantiator() {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected ITermLabel getTermLabel(Term applicationTerm) {
      return SymbolicExecutionUtil.getSymbolicExecutionLabel(applicationTerm);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return SymbolicExecutionTermLabel.NAME.toString();
   }
}