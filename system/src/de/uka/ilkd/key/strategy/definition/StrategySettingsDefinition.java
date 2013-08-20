package de.uka.ilkd.key.strategy.definition;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.gui.configuration.StrategySettings;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;

/**
 * <p>
 * Instances of this class defines how a user interfaces has to look like
 * which edits {@link StrategySettings}.
 * </p>
 * <p>
 * The {@link StrategySettingsDefinition} itself and all its provided sub classes
 * are read-only.
 * </p>
 * <p>
 * Each {@link StrategyFactory} should provide an instance of this class to
 * define the user interface which the user can use to edit 
 * supported {@link StrategySettings} in created {@link Strategy} instances.
 * If a {@link StrategyFactory} provides no {@link StrategySettingsDefinition} an
 * empty user interface or even bedder an error message should be shown to the user. 
 * </p>
 * @author Martin Hentschel
 * @see StrategyFactory
 * @see AbstractStrategyPropertyDefinition
 * @see OneOfStrategyPropertyDefinition
 * @see StrategyPropertyValueDefinition
 */
public class StrategySettingsDefinition {
   /**
    * Defines if a user interface control is shown to edit {@link StrategySettings#getMaxSteps()}.
    */
   private boolean showMaxRuleApplications;
   
   /**
    * The label shown in front of the control to edit {@link StrategySettings#getMaxSteps()}.
    */
   private String maxRuleApplicationsLabel;
   
   /**
    * The label shown in front of the controls to edit {@link StrategyProperties}.
    */
   private String propertiesTitle;
   
   /**
    * Defines the controls to edit {@link StrategyProperties}.
    */
   private ImmutableArray<AbstractStrategyPropertyDefinition> properties;

   /**
    * Constructor.
    * @param propertiesTitle
    * @param properties
    */
   public StrategySettingsDefinition(String propertiesTitle, AbstractStrategyPropertyDefinition... properties) {
      this(true, "Max. Rule Applications", propertiesTitle, properties);
   }

   /**
    * Constructor.
    * @param showMaxRuleApplications Defines if a user interface control is shown to edit {@link StrategySettings#getMaxSteps()}.
    * @param maxRuleApplicationsLabel The label shown in front of the control to edit {@link StrategySettings#getMaxSteps()}.
    * @param propertiesTitle The label shown in front of the controls to edit {@link StrategyProperties}.
    * @param properties Defines the controls to edit {@link StrategyProperties}.
    */
   public StrategySettingsDefinition(boolean showMaxRuleApplications, String maxRuleApplicationsLabel, String propertiesTitle, AbstractStrategyPropertyDefinition... properties) {
      this.showMaxRuleApplications = showMaxRuleApplications;
      this.maxRuleApplicationsLabel = maxRuleApplicationsLabel;
      this.propertiesTitle = propertiesTitle;
      this.properties = new ImmutableArray<AbstractStrategyPropertyDefinition>(properties);
   }

   /**
    * Checks if the user interface control to edit {@link StrategySettings#getMaxSteps()} should be shown or not.
    * @return {@code true} show control, {@code false} do not provide a control.
    */
   public boolean isShowMaxRuleApplications() {
      return showMaxRuleApplications;
   }

   /**
    * Returns the label shown in front of the control to edit {@link StrategySettings#getMaxSteps()}.
    * @return The label shown in front of the control to edit {@link StrategySettings#getMaxSteps()} or {@code null} if no label should be shown.
    */
   public String getMaxRuleApplicationsLabel() {
      return maxRuleApplicationsLabel;
   }

   /**
    * Returns the label shown in front of the controls to edit {@link StrategyProperties}.
    * @return The label shown in front of the controls to edit {@link StrategyProperties} or {@code null} if no label should be shown.
    */
   public String getPropertiesTitle() {
      return propertiesTitle;
   }

   /**
    * Returns the definition of controls to edit {@link StrategyProperties}.
    * @return The definition of controls to edit {@link StrategyProperties}.
    */
   public ImmutableArray<AbstractStrategyPropertyDefinition> getProperties() {
      return properties;
   }
}
