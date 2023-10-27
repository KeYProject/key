/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.definition;

import java.util.ArrayList;

import de.uka.ilkd.key.settings.StrategySettings;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.Triple;

import org.key_project.util.collection.ImmutableArray;

/**
 * <p>
 * Instances of this class defines how a user interfaces has to look like which edits
 * {@link StrategySettings}.
 * </p>
 * <p>
 * The {@link StrategySettingsDefinition} itself and all its provided sub classes are read-only.
 * </p>
 * <p>
 * Each {@link StrategyFactory} should provide an instance of this class to define the user
 * interface which the user can use to edit supported {@link StrategySettings} in created
 * {@link Strategy} instances. If a {@link StrategyFactory} provides no
 * {@link StrategySettingsDefinition} an empty user interface or even bedder an error message should
 * be shown to the user.
 * </p>
 *
 * @author Martin Hentschel
 * @see StrategyFactory
 * @see AbstractStrategyPropertyDefinition
 * @see OneOfStrategyPropertyDefinition
 * @see StrategyPropertyValueDefinition
 */
public class StrategySettingsDefinition {

    private static final ArrayList<Triple<String, Integer, IDefaultStrategyPropertiesFactory>> STD_FURTHER_DEFAULTS;

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
     * The {@link IDefaultStrategyPropertiesFactory} used to create default
     * {@link StrategyProperties}.
     */
    private final IDefaultStrategyPropertiesFactory defaultPropertiesFactory;

    /**
     * Further default settings, for example suitable for simplification. Consists of triples
     * (DEFAULT_NAME, MAX_RULE_APPS, PROPERTIES).
     */
    private final ArrayList<Triple<String, Integer, IDefaultStrategyPropertiesFactory>> furtherDefaults;

    static {
        STD_FURTHER_DEFAULTS =
            new ArrayList<>();

        // Java verification standard preset (tested in TimSort case study)
        STD_FURTHER_DEFAULTS.add(new Triple<>(
            "Java verif. std.", 7000, () -> {
                final StrategyProperties newProps =
                    IDefaultStrategyPropertiesFactory.DEFAULT_FACTORY
                            .createDefaultStrategyProperties();

                newProps.setProperty(StrategyProperties.SPLITTING_OPTIONS_KEY,
                    StrategyProperties.SPLITTING_DELAYED);

                newProps.setProperty(StrategyProperties.LOOP_OPTIONS_KEY,
                    StrategyProperties.LOOP_SCOPE_INV_TACLET);

                newProps.setProperty(StrategyProperties.BLOCK_OPTIONS_KEY,
                    StrategyProperties.BLOCK_CONTRACT_INTERNAL);

                newProps.setProperty(StrategyProperties.METHOD_OPTIONS_KEY,
                    StrategyProperties.METHOD_CONTRACT);

                newProps.setProperty(StrategyProperties.MPS_OPTIONS_KEY,
                    StrategyProperties.MPS_MERGE);

                newProps.setProperty(StrategyProperties.DEP_OPTIONS_KEY,
                    StrategyProperties.DEP_ON);

                newProps.setProperty(StrategyProperties.QUERY_OPTIONS_KEY,
                    StrategyProperties.QUERY_ON);

                newProps.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY,
                    StrategyProperties.NON_LIN_ARITH_DEF_OPS);

                newProps.setProperty(StrategyProperties.OSS_OPTIONS_KEY,
                    StrategyProperties.OSS_ON);

                newProps.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY,
                    StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS);

                newProps.setProperty(StrategyProperties.CLASS_AXIOM_OPTIONS_KEY,
                    StrategyProperties.CLASS_AXIOM_DELAYED);

                return newProps;
            }));

        // Simplification preset
        STD_FURTHER_DEFAULTS.add(new Triple<>(
            "Simplification", 5000, () -> {
                final StrategyProperties newProps =
                    IDefaultStrategyPropertiesFactory.DEFAULT_FACTORY
                            .createDefaultStrategyProperties();

                newProps.setProperty(StrategyProperties.SPLITTING_OPTIONS_KEY,
                    StrategyProperties.SPLITTING_OFF);

                newProps.setProperty(StrategyProperties.LOOP_OPTIONS_KEY,
                    StrategyProperties.LOOP_NONE);

                newProps.setProperty(StrategyProperties.BLOCK_OPTIONS_KEY,
                    StrategyProperties.BLOCK_NONE);

                newProps.setProperty(StrategyProperties.METHOD_OPTIONS_KEY,
                    StrategyProperties.METHOD_NONE);

                newProps.setProperty(StrategyProperties.MPS_MERGE, StrategyProperties.MPS_NONE);

                newProps.setProperty(StrategyProperties.DEP_OPTIONS_KEY,
                    StrategyProperties.DEP_OFF);

                newProps.setProperty(StrategyProperties.QUERY_OPTIONS_KEY,
                    StrategyProperties.QUERY_OFF);

                newProps.setProperty(StrategyProperties.QUERYAXIOM_OPTIONS_KEY,
                    StrategyProperties.QUERYAXIOM_OFF);

                newProps.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY,
                    StrategyProperties.NON_LIN_ARITH_NONE);

                newProps.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY,
                    StrategyProperties.QUANTIFIERS_NONE);

                newProps.setProperty(StrategyProperties.CLASS_AXIOM_OPTIONS_KEY,
                    StrategyProperties.CLASS_AXIOM_OFF);

                return newProps;
            }));
    }

    /**
     * Constructor.
     *
     * @param propertiesTitle The label shown in front of the controls to edit
     *        {@link StrategyProperties}.
     * @param properties Defines the controls to edit {@link StrategyProperties}.
     */
    public StrategySettingsDefinition(String propertiesTitle,
            AbstractStrategyPropertyDefinition... properties) {
        this(true, "Max. Rule Applications", 10000, propertiesTitle,
            IDefaultStrategyPropertiesFactory.DEFAULT_FACTORY, STD_FURTHER_DEFAULTS, properties);
    }

    /**
     * Constructor.
     *
     * @param showMaxRuleApplications Defines if a user interface control is shown to edit
     *        {@link StrategySettings#getMaxSteps()}.
     * @param maxRuleApplicationsLabel The label shown in front of the control to edit
     *        {@link StrategySettings#getMaxSteps()}.
     * @param defaultMaxRuleApplications The default maximal rule applications.
     * @param propertiesTitle The label shown in front of the controls to edit
     *        {@link StrategyProperties}.
     * @param defaultPropertiesFactory The {@link IDefaultStrategyPropertiesFactory} used to create
     *        default {@link StrategyProperties}.
     * @param furtherDefaults further defaults used to create default {@link StrategyProperties}.
     * @param properties Defines the controls to edit {@link StrategyProperties}.
     */
    public StrategySettingsDefinition(boolean showMaxRuleApplications,
            String maxRuleApplicationsLabel, int defaultMaxRuleApplications, String propertiesTitle,
            IDefaultStrategyPropertiesFactory defaultPropertiesFactory,
            ArrayList<Triple<String, Integer, IDefaultStrategyPropertiesFactory>> furtherDefaults,
            AbstractStrategyPropertyDefinition... properties) {
        assert defaultPropertiesFactory != null;
        this.showMaxRuleApplications = showMaxRuleApplications;
        this.maxRuleApplicationsLabel = maxRuleApplicationsLabel;
        this.defaultMaxRuleApplications = defaultMaxRuleApplications;
        this.propertiesTitle = propertiesTitle;
        this.defaultPropertiesFactory = defaultPropertiesFactory;
        this.furtherDefaults = furtherDefaults;
        this.properties = new ImmutableArray<>(properties);
    }

    /**
     * Checks if the user interface control to edit {@link StrategySettings#getMaxSteps()} should be
     * shown or not.
     *
     * @return {@code true} show control, {@code false} do not provide a control.
     */
    public boolean isShowMaxRuleApplications() {
        return showMaxRuleApplications;
    }

    /**
     * Returns the label shown in front of the control to edit
     * {@link StrategySettings#getMaxSteps()}.
     *
     * @return The label shown in front of the control to edit
     *         {@link StrategySettings#getMaxSteps()} or {@code null} if no label should be shown.
     */
    public String getMaxRuleApplicationsLabel() {
        return maxRuleApplicationsLabel;
    }

    /**
     * Returns the label shown in front of the controls to edit {@link StrategyProperties}.
     *
     * @return The label shown in front of the controls to edit {@link StrategyProperties} or
     *         {@code null} if no label should be shown.
     */
    public String getPropertiesTitle() {
        return propertiesTitle;
    }

    /**
     * Returns the definition of controls to edit {@link StrategyProperties}.
     *
     * @return The definition of controls to edit {@link StrategyProperties}.
     */
    public ImmutableArray<AbstractStrategyPropertyDefinition> getProperties() {
        return properties;
    }

    /**
     * Returns the default maximal rule applications.
     *
     * @return The default maximal rule applications.
     */
    public int getDefaultMaxRuleApplications() {
        return defaultMaxRuleApplications;
    }

    /**
     * Returns the {@link IDefaultStrategyPropertiesFactory} used to create default
     * {@link StrategyProperties}.
     *
     * @return The {@link IDefaultStrategyPropertiesFactory} used to create default
     *         {@link StrategyProperties}.
     */
    public IDefaultStrategyPropertiesFactory getDefaultPropertiesFactory() {
        return defaultPropertiesFactory;
    }

    /**
     * @return Further default settings, e.g. for simplification.
     */
    public ArrayList<Triple<String, Integer, IDefaultStrategyPropertiesFactory>> getFurtherDefaults() {
        return furtherDefaults;
    }

}
