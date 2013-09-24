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

package de.uka.ilkd.key.logic.label;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.Name;

/**
 * Label attached to a symbolic execution thread. 
 * Currently realized as singleton. In case one wants to track and distinguish 
 * different lines of execution, this needs to be changed.
 */
public class SymbolicExecutionTermLabel implements ITermLabel {
   /**
    * The unique name of this label.
    */
   public static final Name NAME = new Name("SE");

   /**
    * The name used in {@link Services#getCounter(String)} to keep track
    * of the already used IDs.
    */
   public static final String PROOF_COUNTER_NAME = "SE_LABEL_COUNTER";
   
   /**
    * The unique ID of this term label in the {@link Sequent}.
    */
   private int id;
	
	/**
	 * Constructor.
	 * @param id The unique ID of this term label in the {@link Sequent}.
	 */
	public SymbolicExecutionTermLabel(int id) {
	   this.id = id;
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
		return NAME.toString() + "(" + getId() + ")";
	}

   /**
    * {@inheritDoc}
    */
	@Override
   public Object getChild(int i) {
	   switch (i) {
	      case 0 : return getId();
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
	 * Returns the unique ID of this label in the {@link Sequent}.
	 * @return The unique ID of this label in the {@link Sequent}.
	 */
   public int getId() {
      return id;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Name name() {
      return NAME;
   }
}