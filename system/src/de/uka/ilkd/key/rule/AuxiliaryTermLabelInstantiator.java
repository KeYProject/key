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

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.AuxiliaryTermLabel;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.Term;

/**
 * The {@link ITermLabelWorker} used during prove to define how a
 * {@link AuxiliaryTermLabel} is maintained.
 * @author Christoph Scheben
 */
public final class AuxiliaryTermLabelInstantiator extends AbstractSymbolicExecutionInstantiator {
   /**
    * The only instance of this class.
    */
   public static final AuxiliaryTermLabelInstantiator INSTANCE = new AuxiliaryTermLabelInstantiator();

   /**
    * Constructor to forbid multiple instances.
    */
   private AuxiliaryTermLabelInstantiator() {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected ITermLabel getTermLabel(Term applicationTerm) {
      return AuxiliaryTermLabel.INSTANCE;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return AuxiliaryTermLabel.NAME.toString();
   }
}