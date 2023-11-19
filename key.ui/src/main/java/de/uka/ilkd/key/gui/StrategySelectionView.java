/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.util.*;
import java.util.List;
import java.util.Map.Entry;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.strategy.JavaCardDLStrategy;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.strategy.definition.*;
import de.uka.ilkd.key.util.Triple;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * <p>
 * This {@link JPanel} allows to edit the {@link StrategyProperties} of the
 * {@link JavaCardDLStrategy}. The shown UI controls are generated according to its
 * {@link StrategySettingsDefinition}.
 * </p>
 * <p>
 * <b>There is no need to change this class to change the available settings!</b> The only thing to
 * be done is to modify the available {@link StrategySettingsDefinition} in
 * {@link StrategyFactory#getSettingsDefinition()}.
 * </p>
 * <p>
 * As future work this class should not show a fixed content defined by {@link #DEFINITION}. Instead
 * it should update the UI controls based on the currently active proof and its {@link Profile}
 * since different {@link Profile}s support different {@link Strategy}s with different
 * {@link StrategyProperties}. For more information have a look at:
 * {@code http://i12www.ira.uka.de/~klebanov/mantis/view.php?id=1359}
 * </p>
 *
 * @author Martin Hentschel
 */
public final class StrategySelectionView extends JPanel implements TabPanel {
    private static final Logger LOGGER = LoggerFactory.getLogger(StrategySelectionView.class);

    /**
     * Generated UID.
     */
    private static final long serialVersionUID = -267867794853527874L;

    /**
     * The always used {@link StrategyFactory}.
     */
    private static final StrategyFactory FACTORY = JavaProfile.DEFAULT;

    /**
     * The {@link StrategySettingsDefinition} of {@link #FACTORY} which defines the UI controls to
     * show.
     */
    private static final StrategySettingsDefinition DEFINITION = FACTORY.getSettingsDefinition();

    /**
     * The name of {@link #FACTORY}.
     */
    private static final String JAVACARDDL_STRATEGY_NAME = FACTORY.name().toString();

    /**
     * The {@link KeYMediator} which provides the active proof.
     */
    private KeYMediator mediator;

    /**
     * Allows access to shown UI controls generated according to {@link #DEFINITION}.
     */
    private StrategySelectionComponents components;

    /**
     * Stores whether a chosen predef setting has been changed; in this case, the default button
     * should be activated again.
     */
    private boolean predefChanged = true;

    /**
     * Observe changes on {@link #mediator}.
     */
    private final KeYSelectionListener mediatorListener = new KeYSelectionListener() {

        public void selectedProofChanged(KeYSelectionEvent e) {
            refresh(e.getSource().getSelectedProof());
        }
    };
    private JButton btnGo;

    public StrategySelectionView() {
        layoutPane();
        refresh(mediator == null ? null : mediator.getSelectedProof());
        setVisible(true);
        addComponentListener(new java.awt.event.ComponentAdapter() {
            public void componentShown(java.awt.event.ComponentEvent e) {
                components.getMaxRuleAppSlider().refresh();
            }
        });
        KeYGuiExtensionFacade.installKeyboardShortcuts(mediator, this,
            KeYGuiExtension.KeyboardShortcuts.STRATEGY_SELECTION_VIEW);
    }

    public StrategySelectionView(MainWindow window, KeYMediator mediator) {
        this();
        setMediator(mediator);
        btnGo.setAction(window.getAutoModeAction());
    }

    /**
     * Build everything
     */
    private void layoutPane() {
        assert components == null : "Content can not be created a second time!";
        components = new StrategySelectionComponents();

        JPanel javaDLOptionsPanel = new JPanel();

        JScrollPane javaDLOptionsScrollPane =
            new JScrollPane(javaDLOptionsPanel, ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED,
                ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);

        javaDLOptionsPanel.setEnabled(true);

        this.setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));

        GridBagConstraints gbcpanel5 = new GridBagConstraints();
        final GridBagLayout javaDLOptionsLayout = new GridBagLayout();
        javaDLOptionsPanel.setLayout(javaDLOptionsLayout);

        javaDLOptionsScrollPane.getVerticalScrollBar().setUnitIncrement(10);

        // //////////////////////////////////////////////////////////////////////

        this.btnGo = new JButton();

        JPanel timeout = createDefaultPanel(components);

        JPanel goPanel = new JPanel();
        GridBagLayout goLayout = new GridBagLayout();
        goPanel.setLayout(goLayout);
        goPanel.setAlignmentX(Component.LEFT_ALIGNMENT);

        gbcpanel5.gridx = 1;
        gbcpanel5.gridy = 0;
        gbcpanel5.gridwidth = 1;
        gbcpanel5.gridheight = 1;
        gbcpanel5.fill = GridBagConstraints.NONE;
        gbcpanel5.weightx = 1;
        gbcpanel5.weighty = 0;
        gbcpanel5.anchor = GridBagConstraints.WEST;
        gbcpanel5.insets = new Insets(4, 4, 4, 4);
        goLayout.setConstraints(btnGo, gbcpanel5);
        goPanel.add(btnGo);

        gbcpanel5.gridx = 2;
        gbcpanel5.gridy = 0;
        gbcpanel5.gridwidth = 1;
        gbcpanel5.gridheight = 1;
        gbcpanel5.fill = GridBagConstraints.NONE;
        gbcpanel5.weightx = 1;
        gbcpanel5.weighty = 0;
        gbcpanel5.anchor = GridBagConstraints.WEST;
        gbcpanel5.insets = new Insets(0, 0, 0, 0);

        gbcpanel5.gridx = 3;
        gbcpanel5.gridy = 0;
        gbcpanel5.gridwidth = 1;
        gbcpanel5.gridheight = 1;
        gbcpanel5.fill = GridBagConstraints.NONE;
        gbcpanel5.weightx = 0;
        gbcpanel5.weighty = 0;
        gbcpanel5.anchor = GridBagConstraints.CENTER;
        gbcpanel5.insets = new Insets(0, 0, 0, 0);
        goLayout.setConstraints(timeout, gbcpanel5);
        goPanel.add(timeout);

        fixVerticalSpace(goPanel);

        Box box = Box.createVerticalBox();
        box.add(Box.createVerticalStrut(4));
        box.add(goPanel);
        box.add(Box.createVerticalStrut(8));

        if (DEFINITION.isShowMaxRuleApplications()) {
            MaxRuleAppSlider maxSlider =
                new MaxRuleAppSlider(mediator, DEFINITION.getMaxRuleApplicationsLabel());
            components.setMaxRuleAppSlider(maxSlider);
            maxSlider.addChangeListener(e -> {
                predefChanged = true;
                refreshDefaultButton();
            });
            maxSlider.setAlignmentX(Component.LEFT_ALIGNMENT);
            box.add(maxSlider);
            box.add(Box.createVerticalStrut(8));
        }

        javaDLOptionsScrollPane.setAlignmentX(Component.LEFT_ALIGNMENT);
        box.add(javaDLOptionsScrollPane);

        // //////////////////////////////////////////////////////////////////////

        if (!DEFINITION.getProperties().isEmpty()) {
            javaDLOptionsScrollPane
                    .setBorder(BorderFactory.createTitledBorder(DEFINITION.getPropertiesTitle()));
            javaDLOptionsPanel.setLayout(javaDLOptionsLayout);

            javaDLOptionsScrollPane.getVerticalScrollBar().setUnitIncrement(10);
            javaDLOptionsScrollPane.setAlignmentX(Component.LEFT_ALIGNMENT);
            box.add(javaDLOptionsScrollPane);

            int yCoord = 0;
            for (AbstractStrategyPropertyDefinition definition : DEFINITION.getProperties()) {
                yCoord = createStrategyProperty(components, FACTORY, javaDLOptionsPanel,
                    javaDLOptionsLayout, yCoord, true, definition);
            }

            fixVerticalSpace(javaDLOptionsScrollPane);
        }

        // //////////////////////////////////////////////////////////////////////

        this.add(box);
    }

    private int createStrategyProperty(
            StrategySelectionComponents data, StrategyFactory factory,
            JPanel javaDLOptionsPanel, GridBagLayout javaDLOptionsLayout, int yCoord,
            boolean topLevel, AbstractStrategyPropertyDefinition definition) {

        // Individual options
        if (definition instanceof OneOfStrategyPropertyDefinition oneOfDefinition) {
            ButtonGroup buttonGroup = new ButtonGroup();
            if (!oneOfDefinition.getValues().isEmpty()) {
                data.addPropertyGroup(oneOfDefinition.getApiKey(), buttonGroup);
            }
            ++yCoord;

            JLabel label = new JLabel(oneOfDefinition.getName());
            label.setToolTipText(oneOfDefinition.getTooltip());
            if (topLevel) {
                addJavaDLOption(javaDLOptionsPanel, label, javaDLOptionsLayout, 1, yCoord, 7);

                ++yCoord;

                int gridx = 0;
                int column = 0;
                for (StrategyPropertyValueDefinition valueDefinition : oneOfDefinition
                        .getValues()) {
                    gridx += 2;
                    JRadioButton radioButton =
                        newButton(valueDefinition.getValue(), oneOfDefinition.getApiKey(),
                            valueDefinition.getApiValue(), true, false, factory);
                    data.addPropertyButton(radioButton, oneOfDefinition.getApiKey());
                    radioButton.setToolTipText(valueDefinition.getTooltip());
                    buttonGroup.add(radioButton);
                    addJavaDLOption(javaDLOptionsPanel, radioButton, javaDLOptionsLayout,
                        valueDefinition.getSwingGridx() >= 0 ? valueDefinition.getSwingGridx()
                                : gridx,
                        yCoord,
                        valueDefinition.getSwingWidth() >= 0 ? valueDefinition.getSwingWidth() : 2);
                    column++;
                    if (oneOfDefinition.getColumnsPerRow() >= 0
                            && column % oneOfDefinition.getColumnsPerRow() == 0) {
                        gridx = 0;
                        ++yCoord;
                    }
                }
            } else {
                if (oneOfDefinition.getValues().get(0).getSwingGridx() >= 0) {
                    addJavaDLOption(javaDLOptionsPanel, label, javaDLOptionsLayout, 2, yCoord, 1);

                    int gridx = 0;
                    int column = 0;
                    for (StrategyPropertyValueDefinition valueDefinition : oneOfDefinition
                            .getValues()) {
                        gridx += 2;
                        JRadioButton radioButton =
                            newButton(valueDefinition.getValue(), oneOfDefinition.getApiKey(),
                                valueDefinition.getApiValue(), true, false, factory);
                        data.addPropertyButton(radioButton, oneOfDefinition.getApiKey());
                        radioButton.setToolTipText(valueDefinition.getTooltip());
                        buttonGroup.add(radioButton);
                        addJavaDLOption(javaDLOptionsPanel, radioButton, javaDLOptionsLayout,
                            valueDefinition.getSwingGridx() >= 0 ? valueDefinition.getSwingGridx()
                                    : gridx,
                            yCoord,
                            valueDefinition.getSwingWidth() >= 0 ? valueDefinition.getSwingWidth()
                                    : 2);
                        column++;
                        if (oneOfDefinition.getColumnsPerRow() >= 0
                                && column % oneOfDefinition.getColumnsPerRow() == 0) {
                            gridx = 0;
                            ++yCoord;
                        }
                    }
                } else {
                    JPanel queryAxiomPanel = new JPanel();
                    queryAxiomPanel.add(label);
                    for (StrategyPropertyValueDefinition valueDefinition : oneOfDefinition
                            .getValues()) {
                        JRadioButton radioButton =
                            newButton(valueDefinition.getValue(), oneOfDefinition.getApiKey(),
                                valueDefinition.getApiValue(), true, false, factory);
                        data.addPropertyButton(radioButton, oneOfDefinition.getApiKey());
                        radioButton.setToolTipText(valueDefinition.getTooltip());
                        buttonGroup.add(radioButton);
                        queryAxiomPanel.add(radioButton);
                    }

                    addJavaDLOption(javaDLOptionsPanel, queryAxiomPanel, javaDLOptionsLayout, 2,
                        yCoord, 7);
                }
            }

            ++yCoord;

            addJavaDLOptionSpace(javaDLOptionsPanel, javaDLOptionsLayout, yCoord);
        } else {
            throw new RuntimeException("Unsupported property definition \"" + definition + "\".");
        }
        // Create sub properties
        for (AbstractStrategyPropertyDefinition subProperty : definition.getSubProperties()) {
            yCoord = createStrategyProperty(data, factory, javaDLOptionsPanel, javaDLOptionsLayout,
                yCoord, false, subProperty);
        }
        return yCoord;
    }

    private JRadioButton newButton(String text, final String key, final String command,
            boolean selected, boolean enabled, final StrategyFactory factory) {
        JRadioButton result = new JRadioButton(text);
        result.addActionListener(e -> {
            predefChanged = true;
            StrategyProperties props = getProperties();
            updateStrategySettings(
                mediator.getSelectedProof().getActiveStrategy().name().toString(), props);
        });
        result.setEnabled(enabled);
        result.setActionCommand(command);
        return result;
    }

    private void addJavaDLOptionSpace(JPanel javaDLOptionsPanel, GridBagLayout javaDLOptionsLayout,
            int yCoord) {
        final GridBagConstraints con = new GridBagConstraints();
        con.gridx = 0;
        con.gridy = yCoord;
        con.gridwidth = 9;
        con.gridheight = 1;
        con.fill = GridBagConstraints.HORIZONTAL;
        con.weightx = 1;
        con.weighty = 0;
        con.anchor = GridBagConstraints.CENTER;
        final Component sep = new JLabel();
        javaDLOptionsLayout.setConstraints(sep, con);
        javaDLOptionsPanel.add(sep);
        addJavaDLOption(javaDLOptionsPanel, Box.createRigidArea(new Dimension(4, 4)),
            javaDLOptionsLayout, 0, yCoord, 1);
        addJavaDLOption(javaDLOptionsPanel, Box.createRigidArea(new Dimension(4, 4)),
            javaDLOptionsLayout, 1, yCoord, 1);
    }

    private void addJavaDLOption(JPanel javaDLOptionsPanel, Component widget,
            GridBagLayout javaDLOptionsLayout, int gridx, int gridy, int width) {
        final GridBagConstraints con = new GridBagConstraints();
        con.gridx = gridx;
        con.gridy = gridy;
        con.gridwidth = width;
        con.gridheight = 1;
        con.fill = GridBagConstraints.NONE;
        con.weightx = 0;
        con.weighty = 0;
        con.anchor = GridBagConstraints.WEST;
        javaDLOptionsLayout.setConstraints(widget, con);
        javaDLOptionsPanel.add(widget);
    }

    private void fixVerticalSpace(JComponent comp) {
        comp.setMaximumSize(new Dimension(Integer.MAX_VALUE, comp.getPreferredSize().height));
    }

    private JPanel createDefaultPanel(StrategySelectionComponents components) {
        final JPanel panel = new JPanel();

        final JButton defaultButton = new JButton("Choose Predef");
        components.setDefaultButton(defaultButton);

        final String[] existingPredefs = new String[1 + DEFINITION.getFurtherDefaults().size()];

        existingPredefs[0] = "Defaults";

        int i = 1;
        for (Triple<String, Integer, IDefaultStrategyPropertiesFactory> furtherDefault : DEFINITION
                .getFurtherDefaults()) {
            existingPredefs[i] = furtherDefault.first;
            i++;
        }

        final JComboBox<String> strategyPredefSettingsCmb = new JComboBox<>(existingPredefs);
        strategyPredefSettingsCmb.setSelectedIndex(0);
        components.setPredefsChoiceCmb(strategyPredefSettingsCmb);

        defaultButton.addActionListener(e -> {
            int newMaxSteps = 0;
            StrategyProperties newProps = null;

            final int selIndex = strategyPredefSettingsCmb.getSelectedIndex();
            if (selIndex == 0) {
                newMaxSteps = DEFINITION.getDefaultMaxRuleApplications();
                newProps =
                    DEFINITION.getDefaultPropertiesFactory().createDefaultStrategyProperties();
            } else {
                Triple<String, Integer, IDefaultStrategyPropertiesFactory> chosenDefault =
                    DEFINITION.getFurtherDefaults().get(selIndex - 1);
                newMaxSteps = chosenDefault.second;
                newProps = chosenDefault.third.createDefaultStrategyProperties();
            }

            mediator.getSelectedProof().getSettings().getStrategySettings()
                    .setMaxSteps(newMaxSteps);
            updateStrategySettings(JAVACARDDL_STRATEGY_NAME, newProps);

            predefChanged = false;
            refresh(mediator.getSelectedProof());

        });

        strategyPredefSettingsCmb
                .addItemListener(e -> defaultButton.getActionListeners()[0].actionPerformed(null));

        panel.add(strategyPredefSettingsCmb);
        panel.add(defaultButton);

        return panel;
    }

    public void setMediator(KeYMediator mediator) {
        if (this.mediator != null) {
            this.mediator.removeKeYSelectionListener(mediatorListener);
        }
        this.mediator = mediator;
        if (components.getMaxRuleAppSlider() != null) {
            components.getMaxRuleAppSlider().setMediator(this.mediator);
        }
        if (this.mediator != null) {
            this.mediator.addKeYSelectionListener(mediatorListener);
        }
    }

    /**
     * performs a refresh of all elements in this tab
     */
    public void refresh(Proof proof) {
        if (proof == null) {
            enableAll(false);
        } else {
            if (components.getMaxRuleAppSlider() != null) {
                components.getMaxRuleAppSlider().refresh();
            }
            StrategyProperties sp =
                proof.getSettings().getStrategySettings().getActiveStrategyProperties();
            for (Entry<String, List<JRadioButton>> entry : components.getPropertyButtons()
                    .entrySet()) {
                String value = sp.getProperty(entry.getKey());
                for (JRadioButton button : entry.getValue()) {
                    button.setSelected(Objects.equals(button.getActionCommand(), value));
                }
            }
            enableAll(true);

            refreshDefaultButton();
        }
    }

    private void refreshDefaultButton() {
        if (mediator.getSelectedProof() != null) {
            components.getDefaultButton().setEnabled(predefChanged);
        } else {
            components.getDefaultButton().setEnabled(false);
            components.getStrategyPredefSettingsCmb().setEnabled(false);
        }
    }

    /**
     * enables or disables all components
     *
     * @param enable boolean saying whether to activate or deactivate the components
     */
    private void enableAll(boolean enable) {
        if (components.getMaxRuleAppSlider() != null) {
            components.getMaxRuleAppSlider().setEnabled(enable);
        }
        components.getDefaultButton().setEnabled(enable);
        components.getStrategyPredefSettingsCmb().setEnabled(enable);
        for (Entry<String, List<JRadioButton>> entry : components.getPropertyButtons().entrySet()) {
            for (JRadioButton button : entry.getValue()) {
                button.setEnabled(enable);
            }
        }
    }

    public Strategy getStrategy(String strategyName, Proof proof, StrategyProperties properties) {
        if (mediator != null) {
            for (StrategyFactory s : mediator.getProfile().supportedStrategies()) {
                if (strategyName.equals(s.name().toString())) {
                    return s.create(proof, properties);
                }
            }
            LOGGER.info("Selected Strategy '{}' not found falling back to {}", strategyName,
                mediator.getProfile().getDefaultStrategyFactory().name());
        }
        return mediator != null
                ? mediator.getProfile().getDefaultStrategyFactory().create(proof, properties)
                : proof.getServices().getProfile().getDefaultStrategyFactory().create(proof,
                    properties);
    }

    /**
     * @return the StrategyProperties
     */
    private StrategyProperties getProperties() {
        StrategyProperties p = new StrategyProperties();

        for (Entry<String, ButtonGroup> entry : components.getPropertyGroups().entrySet()) {
            ButtonModel selected = entry.getValue().getSelection();
            if (selected != null) {
                p.setProperty(entry.getKey(), selected.getActionCommand());
            } else {
                p.setProperty(entry.getKey(), DEFINITION.getDefaultPropertiesFactory()
                        .createDefaultStrategyProperties().getProperty(entry.getKey()));
            }
        }

        return p;
    }

    private void updateStrategySettings(String strategyName, StrategyProperties p) {
        final Proof proof = mediator.getSelectedProof();
        final Strategy strategy = getStrategy(strategyName, proof, p);

        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setStrategy(strategy.name());
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(p);

        proof.getSettings().getStrategySettings().setStrategy(strategy.name());
        proof.getSettings().getStrategySettings().setActiveStrategyProperties(p);

        proof.setActiveStrategy(strategy);

        refresh(proof);
    }


    @Override
    public String getTitle() {
        return "Proof Search Strategy";
    }

    @Override
    public JComponent getComponent() {
        return this;
    }

    @Override
    public Icon getIcon() {
        return IconFactory.PROOF_SEARCH_STRATEGY.get(MainWindow.TAB_ICON_SIZE);
    }

    /**
     * Provided via {@link StrategySelectionView} for direct access
     * to created user interface components.
     *
     * @author Martin Hentschel
     */
    private static class StrategySelectionComponents {
        /**
         * Maps a property key to the {@link JRadioButton}s which defines the values.
         */
        private final Map<String, List<JRadioButton>> propertyButtons =
            new HashMap<>();
        /**
         * Maps a property to the used {@link ButtonGroup}.
         */
        private final Map<String, ButtonGroup> propertyGroups = new HashMap<>();
        /**
         * The {@link MaxRuleAppSlider} in which the maximal number of steps is edited.
         */
        private MaxRuleAppSlider maxRuleAppSlider;
        /**
         * The {@link JButton} which restores default values.
         */
        private JButton defaultButton;

        /**
         * The {@link JComboBox} for choosing a predefined value set.
         */
        private JComboBox<String> strategyPredefSettingsCmb;

        /**
         * Returns the {@link MaxRuleAppSlider} in which the maximal number of steps is edited.
         *
         * @return The {@link MaxRuleAppSlider} in which the maximal number of steps is edited.
         */
        public MaxRuleAppSlider getMaxRuleAppSlider() {
            return maxRuleAppSlider;
        }

        /**
         * Sets the {@link MaxRuleAppSlider} in which the maximal number of steps is edited.
         *
         * @param maxRuleAppSlider The {@link MaxRuleAppSlider} in which the maximal number of steps
         *        is edited.
         */
        public void setMaxRuleAppSlider(MaxRuleAppSlider maxRuleAppSlider) {
            this.maxRuleAppSlider = maxRuleAppSlider;
        }

        /**
         * Registers the given {@link JRadioButton} for the given key.
         *
         * @param button The {@link JRadioButton}.
         * @param key The key.
         */
        public void addPropertyButton(JRadioButton button, String key) {
            List<JRadioButton> buttons =
                propertyButtons.computeIfAbsent(key, k -> new LinkedList<>());
            buttons.add(button);
        }

        /**
         * Returns the mapping of property keys to the {@link JRadioButton}s which defines the
         * values.
         *
         * @return The mapping of property keys to the {@link JRadioButton}s which defines the
         *         values.
         */
        public Map<String, List<JRadioButton>> getPropertyButtons() {
            return propertyButtons;
        }

        /**
         * Returns the {@link JButton} which restores default values.
         *
         * @return The {@link JButton} which restores default values.
         */
        public JButton getDefaultButton() {
            return defaultButton;
        }

        /**
         * Sets the {@link JButton} which restores default values.
         *
         * @param defaultButton The {@link JButton} which restores default values.
         */
        public void setDefaultButton(JButton defaultButton) {
            this.defaultButton = defaultButton;
        }

        /**
         * @return The {@link JComboBox} for choosing a predefined value set.
         */
        public JComboBox<String> getStrategyPredefSettingsCmb() {
            return strategyPredefSettingsCmb;
        }

        /**
         * Sets the {@link JComboBox} for choosing a predefined value set.
         *
         * @param strategyPredefSettingsCmb The {@link JComboBox} for choosing a predefined value
         *        set.
         */
        public void setPredefsChoiceCmb(JComboBox<String> strategyPredefSettingsCmb) {
            this.strategyPredefSettingsCmb = strategyPredefSettingsCmb;
        }

        /**
         * Returns the {@link Map} of properties to {@link ButtonGroup}s.
         *
         * @return The {@link Map} of properties to {@link ButtonGroup}s.
         */
        public Map<String, ButtonGroup> getPropertyGroups() {
            return propertyGroups;
        }

        /**
         * Adds the property group.
         *
         * @param property The property.
         * @param group The {@link ButtonGroup}.
         */
        public void addPropertyGroup(String property, ButtonGroup group) {
            propertyGroups.put(property, group);
        }
    }
}
