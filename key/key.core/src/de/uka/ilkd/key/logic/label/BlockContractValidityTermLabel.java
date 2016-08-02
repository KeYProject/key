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

package de.uka.ilkd.key.logic.label;

import de.uka.ilkd.key.logic.Name;

/**
 * Label attached to the modality of the validity branch of a block contract.
 */
public class BlockContractValidityTermLabel implements TermLabel {
   /**
    * The unique name of this label.
    */
   public static final Name NAME = new Name("BC");
   
   /**
    * The name of the exception variable to distinguish normal from exceptional termination.
    */
   private final String exceptionVariableName;

   /**
    * Constructor.
    * @param exceptionVariableName The name of the exception variable to distinguish normal from exceptional termination.
    */
   public BlockContractValidityTermLabel(String exceptionVariableName) {
       this.exceptionVariableName = exceptionVariableName;
   }

   /**
    * {@inheritDoc}
    */
   public boolean equals(Object o) {
       return this == o;
   }

   /**
    * {@inheritDoc}
    */
   public String toString() {
       return NAME.toString() + "(" + getExceptionVariableName() + ")";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Object getChild(int i) {
	   switch (i) {
	      case 0 : return getExceptionVariableName();
  	      default : return null;
	   }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getChildCount() {
      return 1;
   }

   /**
    * Returns the name of the exception variable to distinguish normal from exceptional termination.
    * @return The name of the exception variable to distinguish normal from exceptional termination.
    */
   public String getExceptionVariableName() {
      return exceptionVariableName;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Name name() {
      return NAME;
   }
}