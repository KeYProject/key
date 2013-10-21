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
   private ImmutableArray<StrategyPropertyValueDefinition> values;

   /**
    * Constructor.
    * @param apiKey The key used in KeY's API.
    * @param name The human readable name of the property.
    * @param values The possible {@link StrategyPropertyValueDefinition} which the user can select.
    */
   public OneOfStrategyPropertyDefinition(String apiKey, String name, StrategyPropertyValueDefinition... values) {
      this(apiKey, name, new AbstractStrategyPropertyDefinition[0], values);
   }

   /**
    * Constructor.
    * @param apiKey The key used in KeY's API.
    * @param name The human readable name of the property.
    * @param subProperties Optional children which edits related properties to this.
    * @param values The possible {@link StrategyPropertyValueDefinition} which the user can select.
    */
   public OneOfStrategyPropertyDefinition(String apiKey, String name, AbstractStrategyPropertyDefinition[] subProperties, StrategyPropertyValueDefinition... values) {
      super(apiKey, name, subProperties);
      this.values = new ImmutableArray<StrategyPropertyValueDefinition>(values);
   }

   /**
    * Returns The possible {@link StrategyPropertyValueDefinition} which the user can select.
    * @return The possible {@link StrategyPropertyValueDefinition} which the user can select.
    */
   public ImmutableArray<StrategyPropertyValueDefinition> getValues() {
      return values;
   }
}
