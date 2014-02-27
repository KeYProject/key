package de.uka.ilkd.key.strategy.definition;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.strategy.StrategyProperties;

/**
 * Provides the basic function definition of user interface controls
 * to edit a single key-value-pair in {@link StrategyProperties}.
 * @author Martin Hentschel
 * @see OneOfStrategyPropertyDefinition
 */
public abstract class AbstractStrategyPropertyDefinition {
   /**
    * The key used in KeY's API.
    */
   private final String apiKey;
   
   /**
    * The human readable name of the property.
    */
   private final String name;
   
   /**
    * The optional tooltip text which describes this property.
    */
   private final String tooltip;

   /**
    * Optional children which edits related properties to this.
    * They might be shown different in the user interface.
    */
   private final ImmutableArray<AbstractStrategyPropertyDefinition> subProperties;
   
   /**
    * Constructor.
    * @param apiKey The key used in KeY's API.
    * @param name The human readable name of the property.
    * @param tooltip The optional tooltip text which describes this property.
    * @param subProperties Optional children which edits related properties to this.
    */
   public AbstractStrategyPropertyDefinition(String apiKey, 
                                             String name, 
                                             String tooltip,
                                             AbstractStrategyPropertyDefinition... subProperties) {
      this.apiKey = apiKey;
      this.name = name;
      this.tooltip = tooltip;
      this.subProperties = new ImmutableArray<AbstractStrategyPropertyDefinition>(subProperties);
   }

   /**
    * Returns the key used in KeY's API.
    * @return The key used in KeY's API.
    */
   public String getApiKey() {
      return apiKey;
   }

   /**
    * Returns the human readable name of the property.
    * @return The human readable name of the property.
    */
   public String getName() {
      return name;
   }

   /**
    * Returns the optional tooltip text which describes this property. 
    * @return The optional tooltip text which describes this property.
    */
   public String getTooltip() {
      return tooltip;
   }

   /**
    * Returns children which edits related properties to this.
    * They might be shown different in the user interface.
    * @return The children if available or an empty {@link ImmutableArray} otherwise.
    */
   public ImmutableArray<AbstractStrategyPropertyDefinition> getSubProperties() {
      return subProperties;
   }
}
