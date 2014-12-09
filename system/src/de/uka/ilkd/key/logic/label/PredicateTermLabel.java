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
   private final String id;
   
   /**
    * The optional previous ID of the label this one is derived from.
    */
   private final String beforeId;
   
   /**
    * Constructor.
    * @param majorId The major part of the unique ID.
    * @param minorId The minor part of the unique ID.
    */
   public PredicateTermLabel(int majorId, int minorId) {
       this(majorId, minorId, null);
   }
   
   /**
    * Constructor.
    * @param majorId The major part of the unique ID.
    * @param minorId The minor part of the unique ID.
    * @param beforeId The optional previous ID of the label this one is derived from.
    */
   public PredicateTermLabel(int majorId, int minorId, String beforeId) {
       this.id = majorId + "." + minorId;
       this.beforeId = beforeId;
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
       return NAME.toString() + 
              "(" + 
             getId() + 
             (beforeId != null ? ", " + beforeId : "") +
             ")";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Object getChild(int i) {
	   switch (i) {
	      case 0 : return getId();
	      case 1 : return getBeforeId();
  	      default : return null;
	   }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getChildCount() {
      if (beforeId != null) {
         return 2;
      }
      else {
         return 1;
      }
   }

   /**
    * Returns the unique ID of this label in the {@link Sequent}.
    * @return The unique ID of this label in the {@link Sequent}.
    */
   public String getId() {
      return id;
   }
   
   /**
    * Returns the major part of the unique ID.
    * @return The major part of the unique ID.
    */
   public int getMajorId() {
      int index = id.indexOf(".");
      return Integer.parseInt(id.substring(0, index));
   }
   
   /**
    * Returns the minor part of the unique ID.
    * @return The minor part of the unique ID.
    */
   public int getMinorId() {
      int index = id.indexOf(".");
      return Integer.parseInt(id.substring(index + 1));
   }

   /**
    * Returns the optional previous ID of the label this one is derived from.
    * @return The optional previous ID of the label this one is derived from.
    */
   public String getBeforeId() {
      return beforeId;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Name name() {
      return NAME;
   }
}