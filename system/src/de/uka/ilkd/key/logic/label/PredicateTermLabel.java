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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Sequent;

/**
 * Label attached to a predicates for instance in postconditions, loop invariants or precondition checks of applied operation contracts.
 */
public class PredicateTermLabel implements TermLabel {
   /**
    * The unique name of this label.
    */
   public static final Name NAME = new Name("P");

   /**
    * The name used in {@link Services#getCounter(String)} to keep track
    * of the already used IDs.
    */
   public static final String PROOF_COUNTER_NAME = "P_LABEL_COUNTER";

   /**
    * The prefix of the name used in {@link Services#getCounter(String)} to 
    * keep track of the already used sub IDs.
    */
   public static final String PROOF_COUNTER_SUB_PREFIX = "P_LABEL_SUB_COUNTER_";
   
   /**
    * The unique ID of this term label in the {@link Sequent}.
    */
   private final int id;

   /**
    * The unique sub id of the given id.
    */
   private final int subId;
   
   /**
    * Constructor.
    * @param id The unique ID of this term label in the {@link Sequent}.
    * @param subId The unique sub id of the given id.
    */
   public PredicateTermLabel(int id, int subId) {
       this.id = id;
       this.subId = subId;
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
       return NAME.toString() + "(" + getId() + ", " + getSubId() + ")";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Object getChild(int i) {
	   switch (i) {
	      case 0 : return getId();
         case 1 : return getSubId();
  	      default : return null;
	   }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getChildCount() {
      return 2;
   }

   /**
    * Returns the unique ID of this label in the {@link Sequent}.
    * @return The unique ID of this label in the {@link Sequent}.
    */
   public int getId() {
      return id;
   }

   /**
    * Returns the unique sub id of the given id.
    * @return The unique sub id of the given id.
    */
   public int getSubId() {
      return subId;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Name name() {
      return NAME;
   }
}