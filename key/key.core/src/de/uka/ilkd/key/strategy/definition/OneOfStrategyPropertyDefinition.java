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

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.strategy.StrategyProperties;

/**
 * Defines that a user interface control which edits a single key-value-pair 
 * of the {@link StrategyProperties} allows the user to select predefined values.
 * It might be realized via radio buttons or read-only drop down boxes (combos).
 * @author Martin Hentschel
 * @see AbstractStrategyPropertyDefinition
 * @see StrategyPropertyValueDefinition
 */
public class OneOfStrategyPropertyDefinition extends AbstractStrategyPropertyDefinition {
   /**
    * The possible {@link StrategyPropertyValueDefinition} which the user can select.
    */
   private final ImmutableArray<StrategyPropertyValueDefinition> values;

   /**
    * Defines optionally how many columns are shown per row. 
    * A negative value means unlimited columns.
    */
   private final int columnsPerRow;
   
   /**
    * Constructor.
    * @param apiKey The key used in KeY's API.
    * @param name The human readable name of the property.
    * @param values The possible {@link StrategyPropertyValueDefinition} which the user can select.
    */
   public OneOfStrategyPropertyDefinition(String apiKey, 
                                          String name, 
                                          StrategyPropertyValueDefinition... values) {
      this(apiKey, name, new AbstractStrategyPropertyDefinition[0], values);
   }
   
   /**
    * Constructor.
    * @param apiKey The key used in KeY's API.
    * @param name The human readable name of the property.
    * @param columnsPerRow Defines optionally how many columns are shown per row. 
    * @param values The possible {@link StrategyPropertyValueDefinition} which the user can select.
    */
   public OneOfStrategyPropertyDefinition(String apiKey, 
                                          String name, 
                                          int columnsPerRow, 
                                          StrategyPropertyValueDefinition... values) {
      this(apiKey, name, null, columnsPerRow, new AbstractStrategyPropertyDefinition[0], values);
   }

   /**
    * Constructor.
    * @param apiKey The key used in KeY's API.
    * @param name The human readable name of the property.
    * @param subProperties Optional children which edits related properties to this.
    * @param values The possible {@link StrategyPropertyValueDefinition} which the user can select.
    */
   public OneOfStrategyPropertyDefinition(String apiKey, 
                                          String name, 
                                          AbstractStrategyPropertyDefinition[] subProperties, 
                                          StrategyPropertyValueDefinition... values) {
      this(apiKey, name, null, -1, subProperties, values);
   }

   /**
    * Constructor.
    * @param apiKey The key used in KeY's API.
    * @param name The human readable name of the property.
    * @param tooltip The optional tooltip text which describes this property.
    * @param columnsPerRow Defines optionally how many columns are shown per row. 
    * @param subProperties Optional children which edits related properties to this.
    * @param values The possible {@link StrategyPropertyValueDefinition} which the user can select.
    */
   public OneOfStrategyPropertyDefinition(String apiKey, 
                                          String name, 
                                          String tooltip,
                                          int columnsPerRow, 
                                          AbstractStrategyPropertyDefinition[] subProperties, 
                                          StrategyPropertyValueDefinition... values) {
      super(apiKey, name, tooltip, subProperties);
      this.columnsPerRow = columnsPerRow;
      this.values = new ImmutableArray<StrategyPropertyValueDefinition>(values);
   }

   /**
    * Returns The possible {@link StrategyPropertyValueDefinition} which the user can select.
    * @return The possible {@link StrategyPropertyValueDefinition} which the user can select.
    */
   public ImmutableArray<StrategyPropertyValueDefinition> getValues() {
      return values;
   }

   /**
    * Returns the maximal columns per row.
    * @return The maximal columns per row or a negative value for unlimited columns.
    */
   public int getColumnsPerRow() {
      return columnsPerRow;
   }
}