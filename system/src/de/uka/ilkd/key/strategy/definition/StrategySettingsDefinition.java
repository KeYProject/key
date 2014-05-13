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
   private final boolean showMaxRuleApplications;
   
   /**
    * The label shown in front of the control to edit {@link StrategySettings#getMaxSteps()}.
    */
   private final String maxRuleApplicationsLabel;
   
   /**
    * The label shown in front of the controls to edit {@link StrategyProperties}.
    */
   private final String propertiesTitle;
   
   /**
    * Defines the controls to edit {@link StrategyProperties}.
    */
   private final ImmutableArray<AbstractStrategyPropertyDefinition> properties;

   /**
    * The default maximal rule applications.
    */
   private final int defaultMaxRuleApplications;
   
   /**
    * The {@link IDefaultStrategyPropertiesFactory} used to create default {@link StrategyProperties}.
    */
   private final IDefaultStrategyPropertiesFactory defaultPropertiesFactory;
   
   /**
    * Constructor.
    * @param propertiesTitle The label shown in front of the controls to edit {@link StrategyProperties}.
    * @param properties Defines the controls to edit {@link StrategyProperties}.
    */
   public StrategySettingsDefinition(String propertiesTitle, 
                                     AbstractStrategyPropertyDefinition... properties) {
      this(true, 
           "Max. Rule Applications", 
           10000, 
           propertiesTitle, 
           IDefaultStrategyPropertiesFactory.DEFAULT_FACTORY,
           properties);
   }

   /**
    * Constructor.
    * @param showMaxRuleApplications Defines if a user interface control is shown to edit {@link StrategySettings#getMaxSteps()}.
    * @param maxRuleApplicationsLabel The label shown in front of the control to edit {@link StrategySettings#getMaxSteps()}.
    * @param defaultMaxRuleApplications The default maximal rule applications.
    * @param propertiesTitle The label shown in front of the controls to edit {@link StrategyProperties}.
    * @param defaultPropertiesFactory The {@link IDefaultStrategyPropertiesFactory} used to create default {@link StrategyProperties}.
    * @param properties Defines the controls to edit {@link StrategyProperties}.
    */
   public StrategySettingsDefinition(boolean showMaxRuleApplications, 
                                     String maxRuleApplicationsLabel, 
                                     int defaultMaxRuleApplications,
                                     String propertiesTitle, 
                                     IDefaultStrategyPropertiesFactory defaultPropertiesFactory,
                                     AbstractStrategyPropertyDefinition... properties) {
      assert defaultPropertiesFactory != null;
      this.showMaxRuleApplications = showMaxRuleApplications;
      this.maxRuleApplicationsLabel = maxRuleApplicationsLabel;
      this.defaultMaxRuleApplications = defaultMaxRuleApplications;
      this.propertiesTitle = propertiesTitle;
      this.defaultPropertiesFactory = defaultPropertiesFactory;
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

   /**
    * Returns the default maximal rule applications.
    * @return The default maximal rule applications.
    */
   public int getDefaultMaxRuleApplications() {
      return defaultMaxRuleApplications;
   }

   /**
    * Returns the {@link IDefaultStrategyPropertiesFactory} used to create default {@link StrategyProperties}.
    * @return The {@link IDefaultStrategyPropertiesFactory} used to create default {@link StrategyProperties}.
    */
   public IDefaultStrategyPropertiesFactory getDefaultPropertiesFactory() {
      return defaultPropertiesFactory;
   }
}