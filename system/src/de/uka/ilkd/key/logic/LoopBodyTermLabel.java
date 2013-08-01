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

package de.uka.ilkd.key.logic;

/**
 * Label attached to the modality which executes a loop body 
 * in branch "Body Preserves Invariant" of applied "Loop Invariant" rules. 
 */
public class LoopBodyTermLabel implements ITermLabel {
   /**
    * The unique name of this label.
    */
   public static final Name NAME = new Name("LoopBody");

   /**
    * The only instance of this class.
    */
	public static LoopBodyTermLabel INSTANCE = new LoopBodyTermLabel();
	
	/**
	 * Constructor to forbid multiple instances.
	 */
	private LoopBodyTermLabel() {		
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
		return NAME.toString();
	}

   /**
    * {@inheritDoc}
    */
	@Override
   public ITermLabel getChild(int i) {
      return null;
   }

   /**
    * {@inheritDoc}
    */
	@Override
   public int getChildCount() {
      return 0;
   }

	/**
	 * {@inheritDoc}
	 */
   @Override
   public Name name() {
      return NAME;
   }
}