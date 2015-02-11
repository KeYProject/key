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

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Sequent;

/**
 * Label attached to a predicates for instance in postconditions, loop invariants or precondition checks of applied operation contracts.
 */
public class FormulaTermLabel implements TermLabel {
   /**
    * The unique name of this label.
    */
   public static final Name NAME = new Name("F");

   /**
    * The name used in {@link Services#getCounter(String)} to keep track
    * of the already used IDs.
    */
   public static final String PROOF_COUNTER_NAME = "F_LABEL_COUNTER";

   /**
    * The prefix of the name used in {@link Services#getCounter(String)} to 
    * keep track of the already used sub IDs.
    */
   public static final String PROOF_COUNTER_SUB_PREFIX = "F_LABEL_SUB_COUNTER_";
   
   /**
    * Separator between multiple before IDs.
    */
   public static final String BEFORE_ID_SEPARATOR = ";";
   
   /**
    * The unique major ID of this term label in the {@link Sequent}.
    */
   private final int majorId;
   
   /**
    * The per major ID unique minor ID of this term label in the {@link Sequent}.
    */
   private final int minorId;
   
   /**
    * The optional previous IDs of the label this one is derived from separated by {@value #BEFORE_ID_SEPARATOR}.
    */
   private final String beforeIds;
   
   /**
    * Constructor.
    * @param id The unique ID of this term label in the {@link Sequent}.
    * @throws TermLabelException Occurred Exception in case that the given ID is not valid.
    */
   public FormulaTermLabel(String id) throws TermLabelException {
      this(getMajorId(id), getMinorId(id));
   }
   
   /**
    * Constructor.
    * @param id The unique ID of this term label in the {@link Sequent}.
    * @param beforeIds The optional previous IDs of the label this one is derived from separated by {@value #BEFORE_ID_SEPARATOR}.
    * @throws TermLabelException Occurred Exception in case that the given IDs are not valid.
    */
   public FormulaTermLabel(String id, String beforeIds) throws TermLabelException {
      this(getMajorId(id), 
           getMinorId(id),
           getValidBeforeIds(beforeIds)); // Ensure that before IDs are valid.
   }
   
   /**
    * Constructor.
    * @param majorId The major part of the unique ID.
    * @param minorId The minor part of the unique ID.
    */
   public FormulaTermLabel(int majorId, int minorId) {
       this(majorId, minorId, null);
   }
   
   /**
    * Constructor.
    * @param majorId The major part of the unique ID.
    * @param minorId The minor part of the unique ID.
    * @param beforeIds The optional previous ID of the label this one is derived from.
    */
   public FormulaTermLabel(int majorId, int minorId, Collection<String> beforeIds) {
       this.majorId = majorId;
       this.minorId = minorId;
       if (beforeIds != null && !beforeIds.isEmpty()) {
          StringBuffer sb = new StringBuffer();
          boolean afterFirst = false;
          for (String id : beforeIds) {
             if (id != null) {
                if (afterFirst) {
                   sb.append(BEFORE_ID_SEPARATOR);
                }
                else {
                   afterFirst = true;
                }
                sb.append(id);
             }
          }
          this.beforeIds = sb.toString();
       }
       else {
          this.beforeIds = null;
       }
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
              (beforeIds != null ? ", " + beforeIds : "") +
              ")";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Object getChild(int i) {
	   switch (i) {
	      case 0 : return getId();
	      case 1 : return beforeIds;
  	      default : return null;
	   }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getChildCount() {
      if (beforeIds != null) {
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
      return majorId + "." + minorId;
   }
   
   /**
    * Returns the major part of the unique ID.
    * @return The major part of the unique ID.
    */
   public int getMajorId() {
      return majorId;
   }
   
   /**
    * Returns the major part of the given ID.
    * @param id The ID to extract its major part.
    * @return The major part of the given ID.
    * @throws TermLabelException Occurred Exception in case that the given ID is not valid.
    */
   public static int getMajorId(String id) throws TermLabelException {
      int index = id.indexOf(".");
      if (index < 0) {
         throw new TermLabelException("The ID '" + id + "' is not separated into major and minor ID by '.'.");
      }
      try {
         return Integer.parseInt(id.substring(0, index));
      }
      catch (NumberFormatException e) {
         throw new TermLabelException("The major ID of '" + id + "' is not a valid integer.");
      }
   }
   
   /**
    * Returns the minor part of the unique ID.
    * @return The minor part of the unique ID.
    */
   public int getMinorId() {
      return minorId;
   }
   
   /**
    * Returns the minor part of the given ID.
    * @param id The ID to extract its minor part.
    * @return The minor part of the given ID.
    * @throws TermLabelException Occurred Exception in case that the given ID is not valid.
    */
   public static int getMinorId(String id) throws TermLabelException {
      int index = id.indexOf(".");
      if (index < 0) {
         throw new TermLabelException("The ID '" + id + "' is not separated into major and minor ID by '.'.");
      }
      try {
         return Integer.parseInt(id.substring(index + 1));
      }
      catch (NumberFormatException e) {
         throw new TermLabelException("The minor ID of '" + id + "' is not a valid integer.");
      }
   }

   /**
    * Returns the optional previous IDs of the label this one is derived from.
    * @return The optional previous IDs of the label this one is derived from.
    */
   public String[] getBeforeIds() {
      return getBeforeIds(beforeIds);
   }
   
   /**
    * Returns the optional previous IDs of the label this one is derived from.
    * @param beforeIds The {@link String} with the before IDs.
    * @return The optional previous IDs of the label this one is derived from.
    */
   private static String[] getBeforeIds(String beforeIds) {
      return beforeIds != null ? 
             beforeIds.split(BEFORE_ID_SEPARATOR) : 
             new String[0];
   }
   
   /**
    * Returns the optional previous IDs if they are all valid.
    * @param beforeIds The {@link String} with the before IDs to analyze.
    * @return The valid before IDs.
    * @throws TermLabelException Occurred Exception in case that the given IDs are not valid.
    */
   public static List<String> getValidBeforeIds(String beforeIds) throws TermLabelException {
      if (beforeIds == null || beforeIds.isEmpty()) {
         throw new TermLabelException("No before IDs defined.");
      }
      List<String> result = new LinkedList<String>();
      String[] candidates = getBeforeIds(beforeIds);
      for (String id : candidates) {
         if (!id.isEmpty()) {
            getMinorId(id); // Validate minor ID.
            getMajorId(id); // Validate major ID.
            result.add(id);
         }
         else {
            throw new TermLabelException("Empty entry in beforeIds '" + beforeIds + "' found.");
         }
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Name name() {
      return NAME;
   }

   /**
    * Creates a new label sub ID.
    * @param services The {@link Services} to use.
    * @param label The parent {@link FormulaTermLabel} which provides the major ID.
    * @return The new label sub ID.
    */
   public static int newLabelSubID(Services services, FormulaTermLabel label) {
      return newLabelSubID(services, label.getMajorId());
   }

   /**
    * Creates a new label sub ID.
    * @param services The {@link Services} to use.
    * @param labelId The parent {@link FormulaTermLabel} which provides the major ID.
    * @return The new label sub ID.
    */
   public static int newLabelSubID(Services services, int labelId) {
      return services.getCounter(FormulaTermLabel.PROOF_COUNTER_SUB_PREFIX + labelId).getCountPlusPlus();
   }
}