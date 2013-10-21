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
   private String apiValue;
   
   /**
    * The human readable value shown in the user interface control.
    */
   private String value;
   
   /**
    * The optional tooltip text which describes this value.
    */
   private String tooltip;

   /**
    * Constructor.
    * @param apiValue
    * @param value
    * @param tooltip
    */
   public StrategyPropertyValueDefinition(String apiValue, String value, String tooltip) {
      this.apiValue = apiValue;
      this.value = value;
      this.tooltip = tooltip;
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
}