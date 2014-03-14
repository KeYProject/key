package de.uka.ilkd.key.strategy.definition;

import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyProperties;

/**
 * Instances of this factory are used to create default {@link StrategyProperties}
 * used by a {@link Strategy} defined via its {@link StrategySettingsDefinition}.
 * @author Martin Hentschel
 */
public interface IDefaultStrategyPropertiesFactory {
   /**
    * The default implementation.
    */
   public static IDefaultStrategyPropertiesFactory DEFAULT_FACTORY = new IDefaultStrategyPropertiesFactory() {
      @Override
      public StrategyProperties createDefaultStrategyProperties() {
         return new StrategyProperties();
      }
   };
   
   /**
    * Creates new default {@link StrategyProperties}.
    * @return The new default {@link StrategyProperties}.
    */
   public StrategyProperties createDefaultStrategyProperties();
}
