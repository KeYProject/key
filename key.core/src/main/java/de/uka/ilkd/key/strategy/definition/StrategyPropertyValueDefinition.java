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

package de.uka.ilkd.key.strategy.definition;

/**
 * Defines a single value a user can select in the user interface control
 * defined by a {@link OneOfStrategyPropertyDefinition}.
 * @author Martin Hentschel
 * @see OneOfStrategyPropertyDefinition
 */
public class StrategyPropertyValueDefinition {
   /**
    * The value used by KeY's API.
    */
   private final String apiValue;
   
   /**
    * The human readable value shown in the user interface control.
    */
   private final String value;
   
   /**
    * The optional tooltip text which describes this value.
    */
   private final String tooltip;
   
   /**
    * The optional hint for Swing user interfaces how to place the control used to edit the represented settings value.
    * A negative number means that it is not defined.
    */
   private final int swingGridx;
   
   private final int swingWidth;

   /**
    * Constructor.
    * @param apiValue The value used by KeY's API.
    * @param value The human readable value shown in the user interface control.
    * @param tooltip The optional tooltip text which describes this value.
    */
   public StrategyPropertyValueDefinition(String apiValue, String value, String tooltip) {
      this(apiValue, value, tooltip, -1, -1);
   }

   /**
    * Constructor.
    * @param apiValue The value used by KeY's API.
    * @param value The human readable value shown in the user interface control.
    * @param tooltip The optional tooltip text which describes this value.
    * @param swingGridx The optional hint for Swing user interfaces how to place the control used to edit the represented settings value or a negative number if not defined.
    */
   public StrategyPropertyValueDefinition(String apiValue, 
                                          String value, 
                                          String tooltip, 
                                          int swingGridx,
                                          int swingWidth) {
      this.apiValue = apiValue;
      this.value = value;
      this.tooltip = tooltip;
      this.swingGridx = swingGridx;
      this.swingWidth = swingWidth;
   }

   /**
    * Returns The value used by KeY's API.
    * @return The value used by KeY's API.
    */
   public String getApiValue() {
      return apiValue;
   }

   /**
    * Returns The human readable value shown in the user interface control.
    * @return The human readable value shown in the user interface control.
    */
   public String getValue() {
      return value;
   }

   /**
    * Returns The optional tooltip text which describes this value.
    * @return The optional tooltip text which describes this value.
    */
   public String getTooltip() {
      return tooltip;
   }

   /**
    * Returns the optional hint for Swing user interfaces how to place the control used to edit the represented settings value.
    * @return The optional hint for Swing user interfaces how to place the control used to edit the represented settings value or a negative number if not defined.
    */
   public int getSwingGridx() {
      return swingGridx;
   }

   public int getSwingWidth() {
      return swingWidth;
   }
}