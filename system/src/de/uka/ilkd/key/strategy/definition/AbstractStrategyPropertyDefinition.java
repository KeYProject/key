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
   private String apiKey;
   
   /**
    * The human readable name of the property.
    */
   private String name;

   /**
    * Optional children which edits related properties to this.
    * They might be shown different in the user interface.
    */
   private ImmutableArray<AbstractStrategyPropertyDefinition> subProperties;
   
   /**
    * Constructor.
    * @param apiKey The key used in KeY's API.
    * @param name The human readable name of the property.
    * @param subProperties Optional children which edits related properties to this.
    */
   public AbstractStrategyPropertyDefinition(String apiKey, 
                                   String name, 
                                   AbstractStrategyPropertyDefinition... subProperties) {
      this.apiKey = apiKey;
      this.name = name;
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
    * Returns children which edits related properties to this.
    * They might be shown different in the user interface.
    * @return The children if available or an empty {@link ImmutableArray} otherwise.
    */
   public ImmutableArray<AbstractStrategyPropertyDefinition> getSubProperties() {
      return subProperties;
   }
}
