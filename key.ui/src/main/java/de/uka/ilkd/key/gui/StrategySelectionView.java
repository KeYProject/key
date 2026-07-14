/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.*;
import java.util.List;
import java.util.Map.Entry;
import java.util.function.Supplier;
import javax.swing.*;
import javax.swing.plaf.basic.ComboPopup;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.settings.StrategyPresetsSettings;
import de.uka.ilkd.key.settings.StrategyPresetsSettings.StrategyPreset;
import de.uka.ilkd.key.strategy.JavaCardDLStrategy;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.strategy.definition.*;

import org.jspecify.annotations.NonNull;
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
    private static final StrategyFactory FACTORY = JavaProfile.getDefault();

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
     * Set while the preset combo box is being rebuilt or reselected programmatically. Guards the
     * combo box listeners so that they do not (re-)apply a preset in reaction to our own changes.
     */
    private boolean adjustingPresetCombo = false;

    /**
     * One-shot guard spanning a delete-via-"x" interaction. The popup commits its selection on
     * mouse release <em>after</em> our press handler has already deleted the preset; this flag
     * keeps
     * that trailing commit from applying a preset. Reset on the next idle EDT cycle.
     */
    private boolean suppressPresetApply = false;

    /**
     * The combo box popup list, cached once the delete handler is installed, so the delete action
     * can keep the popup selection aligned with the combo box.
     */
    private JList<?> presetPopupList;

    /**
     * Width (in pixels) of the clickable delete zone drawn at the right edge of user-defined preset
     * rows in the combo box popup.
     */
    private static final int PRESET_DELETE_ZONE_WIDTH = 26;

    /**
     * Colour of the "x" delete affordance while its zone is hovered.
     */
    private static final Color PRESET_DELETE_ACTIVE_COLOR = new Color(0xCC, 0x33, 0x33);

    /**
     * Whether the mouse handler for the preset combo box popup has already been installed. The
     * popup list only exists once the popup has been shown for the first time.
     */
    private boolean presetDeleteHandlerInstalled = false;

    /**
     * Index of the combo box popup row whose delete zone is currently hovered, or {@code -1}.
     */
    private int presetDeleteRolloverIndex = -1;

    /**
     * Observe changes on {@link #mediator}.
     */
    private final KeYSelectionListener mediatorListener = new KeYSelectionListener() {

        public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
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
        this.btnGo.putClientProperty("isAutoButton", Boolean.TRUE);

        JPanel timeout = createDefaultPanel(components);

        JPanel goPanel = new JPanel();
        GridBagLayout goLayout = new GridBagLayout();
        goPanel.setLayout(goLayout);
        goPanel.setAlignmentX(LEFT_ALIGNMENT);

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
            maxSlider.setAlignmentX(LEFT_ALIGNMENT);
            box.add(maxSlider);
            box.add(Box.createVerticalStrut(8));
        }

        javaDLOptionsScrollPane.setAlignmentX(LEFT_ALIGNMENT);
        box.add(javaDLOptionsScrollPane);

        // //////////////////////////////////////////////////////////////////////

        if (!DEFINITION.getProperties().isEmpty()) {
            javaDLOptionsScrollPane
                    .setBorder(BorderFactory.createTitledBorder(DEFINITION.getPropertiesTitle()));
            javaDLOptionsPanel.setLayout(javaDLOptionsLayout);

            javaDLOptionsScrollPane.getVerticalScrollBar().setUnitIncrement(10);
            javaDLOptionsScrollPane.setAlignmentX(LEFT_ALIGNMENT);
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

        final JButton defaultButton = new JButton("Apply");
        // Keep the button compact: trim the internal padding a little.
        defaultButton.setMargin(new Insets(2, 8, 2, 8));
        components.setDefaultButton(defaultButton);

        final JComboBox<PresetEntry> strategyPredefSettingsCmb = new JComboBox<>();
        strategyPredefSettingsCmb.setRenderer(new PresetListCellRenderer());
        components.setPredefsChoiceCmb(strategyPredefSettingsCmb);

        // "Choose Predef" applies the currently selected preset.
        defaultButton.addActionListener(e -> applySelectedPreset());

        // Selecting an entry in the combo box applies it immediately, unless we are rebuilding the
        // model ourselves (adding, deleting or renaming a preset must not change the live
        // settings).
        strategyPredefSettingsCmb.addActionListener(e -> {
            if (!adjustingPresetCombo && !suppressPresetApply) {
                applySelectedPreset();
            }
        });

        // Clicking the small "x" on a user-defined row inside the popup deletes that preset.
        installPresetDeleteHandler(strategyPredefSettingsCmb);

        // Adjacent menu button offering save / stash / rename.
        final JButton presetMenuButton = createPresetMenuButton();
        components.setPresetMenuButton(presetMenuButton);

        rebuildPresetCombo(null);

        // Lay the row out as [gear] [combo] [Apply] and give the two buttons the same height as
        // the combo box so the row is flush instead of vertically staggered.
        int rowHeight = strategyPredefSettingsCmb.getPreferredSize().height;
        setPreferredHeight(presetMenuButton, rowHeight);
        setPreferredHeight(defaultButton, rowHeight);

        panel.add(presetMenuButton);
        panel.add(strategyPredefSettingsCmb);
        panel.add(defaultButton);

        return panel;
    }

    /**
     * Fixes the preferred height of the given component while keeping its preferred width, so it
     * can
     * be aligned in height with a neighbouring component.
     */
    private static void setPreferredHeight(JComponent comp, int height) {
        Dimension pref = comp.getPreferredSize();
        comp.setPreferredSize(new Dimension(pref.width, height));
    }

    /**
     * @return the proof-independent settings storing the user-defined strategy presets
     */
    private static StrategyPresetsSettings getPresetsSettings() {
        return ProofIndependentSettings.DEFAULT_INSTANCE.getStrategyPresetsSettings();
    }

    /**
     * Builds the list of combo box entries: the built-in "Defaults", the further built-in presets
     * defined by the profile, followed by the user-defined presets.
     */
    private List<PresetEntry> buildPresetEntries() {
        List<PresetEntry> entries = new ArrayList<>();
        entries.add(PresetEntry.defaults());
        for (StrategySettingsDefinition.StrategySettingEntry e : DEFINITION.getFurtherDefaults()) {
            entries.add(PresetEntry.builtIn(e));
        }
        for (StrategyPreset p : getPresetsSettings().getPresets()) {
            entries.add(PresetEntry.user(p));
        }
        return entries;
    }

    /**
     * Rebuilds the preset combo box model from the built-in and stored presets without touching the
     * live strategy settings.
     *
     * @param selectName the name of the preset to select afterwards, or {@code null} to select the
     *        first entry ("Defaults")
     */
    private void rebuildPresetCombo(String selectName) {
        JComboBox<PresetEntry> combo = components.getStrategyPredefSettingsCmb();
        if (combo == null) {
            return;
        }
        List<PresetEntry> entries = buildPresetEntries();
        adjustingPresetCombo = true;
        try {
            combo.setModel(new DefaultComboBoxModel<>(entries.toArray(new PresetEntry[0])));
            PresetEntry toSelect = null;
            if (selectName != null) {
                for (PresetEntry e : entries) {
                    if (e.name().equals(selectName)) {
                        toSelect = e;
                        break;
                    }
                }
            }
            if (toSelect == null && !entries.isEmpty()) {
                toSelect = entries.get(0);
            }
            combo.setSelectedItem(toSelect);
        } finally {
            adjustingPresetCombo = false;
        }
    }

    /**
     * Applies the preset currently selected in the combo box to the active proof.
     */
    private void applySelectedPreset() {
        if (mediator == null || mediator.getSelectedProof() == null) {
            return;
        }
        PresetEntry entry =
            (PresetEntry) components.getStrategyPredefSettingsCmb().getSelectedItem();
        if (entry == null) {
            return;
        }
        mediator.getSelectedProof().getSettings().getStrategySettings()
                .setMaxSteps(entry.maxSteps());
        predefChanged = false;
        updateStrategySettings(JAVACARDDL_STRATEGY_NAME, entry.properties());
    }

    /**
     * Captures the strategy properties currently reflected by the UI. Starts from the complete
     * active properties of the proof and overlays the values shown by the option controls, so that
     * unsaved manual edits are included while properties without a control keep their value.
     */
    private StrategyProperties currentStrategyProperties() {
        StrategyProperties base = mediator.getSelectedProof().getSettings().getStrategySettings()
                .getActiveStrategyProperties();
        StrategyProperties displayed = getProperties();
        for (String key : displayed.stringPropertyNames()) {
            base.setProperty(key, displayed.getProperty(key));
        }
        return base;
    }

    /**
     * @return the maximal number of rule applications currently configured for the active proof
     */
    private int currentMaxSteps() {
        return mediator.getSelectedProof().getSettings().getStrategySettings().getMaxSteps();
    }

    /**
     * @param name a candidate preset name
     * @return {@code true} if the name is used by a built-in preset (and thus reserved)
     */
    private boolean isBuiltInName(String name) {
        if ("Defaults".equals(name)) {
            return true;
        }
        for (StrategySettingsDefinition.StrategySettingEntry e : DEFINITION.getFurtherDefaults()) {
            if (e.name().equals(name)) {
                return true;
            }
        }
        return false;
    }

    private JButton createPresetMenuButton() {
        final JButton button = new JButton("⚙");
        // The gear is a Unicode glyph; enlarge it relative to the default font so it reads well.
        button.setFont(button.getFont().deriveFont(button.getFont().getSize2D() + 6f));
        button.setMargin(new Insets(2, 8, 2, 8));
        button.setToolTipText("Save, stash or rename presets");
        button.addActionListener(e -> showPresetMenu(button));
        return button;
    }

    private void showPresetMenu(JComponent invoker) {
        final boolean hasProof = mediator != null && mediator.getSelectedProof() != null;
        final PresetEntry selected =
            (PresetEntry) components.getStrategyPredefSettingsCmb().getSelectedItem();

        JPopupMenu menu = new JPopupMenu();

        JMenuItem saveAs = new JMenuItem("Save current as…");
        saveAs.setEnabled(hasProof);
        saveAs.addActionListener(e -> saveCurrentAs());
        menu.add(saveAs);

        JMenuItem stash = new JMenuItem("Stash current");
        stash.setToolTipText("Save the current settings to the reusable \"Stash\" preset");
        stash.setEnabled(hasProof);
        stash.addActionListener(e -> stashCurrent());
        menu.add(stash);

        menu.addSeparator();

        JMenuItem rename = new JMenuItem("Rename selected…");
        rename.setEnabled(selected != null && selected.userDefined());
        rename.addActionListener(e -> renameSelected());
        menu.add(rename);

        menu.show(invoker, 0, invoker.getHeight());
    }

    private void saveCurrentAs() {
        if (mediator == null || mediator.getSelectedProof() == null) {
            return;
        }
        Object input = JOptionPane.showInputDialog(this, "Preset name:", "Save strategy preset",
            JOptionPane.PLAIN_MESSAGE, null, null, "");
        if (input == null) {
            return;
        }
        String name = input.toString().trim();
        if (name.isEmpty()) {
            return;
        }
        if (isBuiltInName(name)) {
            JOptionPane.showMessageDialog(this,
                "\"" + name + "\" is the name of a built-in preset. Please choose another name.",
                "Save strategy preset", JOptionPane.WARNING_MESSAGE);
            return;
        }
        StrategyPresetsSettings settings = getPresetsSettings();
        if (settings.contains(name)) {
            int choice = JOptionPane.showConfirmDialog(this,
                "A preset named \"" + name + "\" already exists. Overwrite it?",
                "Overwrite strategy preset", JOptionPane.YES_NO_OPTION);
            if (choice != JOptionPane.YES_OPTION) {
                return;
            }
        }
        settings.saveOrUpdate(
            new StrategyPreset(name, currentMaxSteps(), currentStrategyProperties()));
        rebuildPresetCombo(name);
    }

    private void stashCurrent() {
        if (mediator == null || mediator.getSelectedProof() == null) {
            return;
        }
        getPresetsSettings().stash(currentMaxSteps(), currentStrategyProperties());
        rebuildPresetCombo(StrategyPresetsSettings.STASH_NAME);
    }

    private void renameSelected() {
        PresetEntry selected =
            (PresetEntry) components.getStrategyPredefSettingsCmb().getSelectedItem();
        if (selected == null || !selected.userDefined()) {
            return;
        }
        Object input = JOptionPane.showInputDialog(this, "New name:", "Rename strategy preset",
            JOptionPane.PLAIN_MESSAGE, null, null, selected.name());
        if (input == null) {
            return;
        }
        String newName = input.toString().trim();
        if (newName.isEmpty() || newName.equals(selected.name())) {
            return;
        }
        if (isBuiltInName(newName)) {
            JOptionPane.showMessageDialog(this,
                "\"" + newName + "\" is the name of a built-in preset. Please choose another name.",
                "Rename strategy preset", JOptionPane.WARNING_MESSAGE);
            return;
        }
        if (getPresetsSettings().contains(newName)) {
            JOptionPane.showMessageDialog(this,
                "A preset named \"" + newName + "\" already exists.",
                "Rename strategy preset", JOptionPane.WARNING_MESSAGE);
            return;
        }
        getPresetsSettings().rename(selected.name(), newName);
        rebuildPresetCombo(newName);
    }

    private void deleteUserPreset(PresetEntry entry) {
        if (entry == null || !entry.userDefined()) {
            return;
        }
        JComboBox<PresetEntry> combo = components.getStrategyPredefSettingsCmb();
        PresetEntry selected = (PresetEntry) combo.getSelectedItem();
        String keepSelected =
            (selected != null && !selected.name().equals(entry.name())) ? selected.name() : null;
        getPresetsSettings().remove(entry.name());
        rebuildPresetCombo(keepSelected);
        // Keep the popup list's selection aligned with the combo box so that a trailing
        // mouse-release commit (if any) re-selects the same entry instead of an arbitrary row.
        if (presetPopupList != null) {
            presetPopupList.setSelectedIndex(combo.getSelectedIndex());
        }
    }

    /**
     * Installs, lazily on first popup opening, a mouse handler on the combo box popup list that
     * deletes a user-defined preset when its trailing "x" is clicked and highlights the delete zone
     * on hover.
     */
    private void installPresetDeleteHandler(JComboBox<PresetEntry> combo) {
        combo.addPopupMenuListener(new javax.swing.event.PopupMenuListener() {
            @Override
            public void popupMenuWillBecomeVisible(javax.swing.event.PopupMenuEvent e) {
                if (presetDeleteHandlerInstalled) {
                    return;
                }
                var child = combo.getUI().getAccessibleChild(combo, 0);
                if (child instanceof ComboPopup popup) {
                    attachPresetDeleteMouseListener(combo, popup.getList());
                    presetDeleteHandlerInstalled = true;
                } else {
                    LOGGER.warn("Could not install preset delete handler: unexpected popup {}",
                        child);
                }
            }

            @Override
            public void popupMenuWillBecomeInvisible(javax.swing.event.PopupMenuEvent e) {
                presetDeleteRolloverIndex = -1;
            }

            @Override
            public void popupMenuCanceled(javax.swing.event.PopupMenuEvent e) {
                presetDeleteRolloverIndex = -1;
            }
        });
    }

    private void attachPresetDeleteMouseListener(JComboBox<PresetEntry> combo, JList<?> list) {
        presetPopupList = list;
        list.addMouseListener(new MouseAdapter() {
            @Override
            public void mousePressed(MouseEvent e) {
                int index = list.locationToIndex(e.getPoint());
                if (index < 0) {
                    return;
                }
                Object value = list.getModel().getElementAt(index);
                Rectangle bounds = list.getCellBounds(index, index);
                if (value instanceof PresetEntry entry && entry.userDefined() && bounds != null
                        && e.getX() >= bounds.x + bounds.width - PRESET_DELETE_ZONE_WIDTH) {
                    e.consume();
                    presetDeleteRolloverIndex = -1;
                    // Guard against the popup's trailing mouse-release committing a selection.
                    suppressPresetApply = true;
                    combo.setPopupVisible(false);
                    deleteUserPreset(entry);
                    SwingUtilities.invokeLater(() -> suppressPresetApply = false);
                }
            }
        });
        list.addMouseMotionListener(new MouseAdapter() {
            @Override
            public void mouseMoved(MouseEvent e) {
                int index = list.locationToIndex(e.getPoint());
                int rollover = -1;
                if (index >= 0) {
                    Object value = list.getModel().getElementAt(index);
                    Rectangle bounds = list.getCellBounds(index, index);
                    if (value instanceof PresetEntry entry && entry.userDefined() && bounds != null
                            && e.getX() >= bounds.x + bounds.width - PRESET_DELETE_ZONE_WIDTH) {
                        rollover = index;
                    }
                }
                if (rollover != presetDeleteRolloverIndex) {
                    presetDeleteRolloverIndex = rollover;
                    list.repaint();
                }
            }
        });
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
            if (components.getPresetMenuButton() != null) {
                components.getPresetMenuButton().setEnabled(false);
            }
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
        if (components.getPresetMenuButton() != null) {
            components.getPresetMenuButton().setEnabled(enable);
        }
        for (Entry<String, List<JRadioButton>> entry : components.getPropertyButtons().entrySet()) {
            for (JRadioButton button : entry.getValue()) {
                button.setEnabled(enable);
            }
        }
    }

    public Strategy<@NonNull Goal> getStrategy(String strategyName, Proof proof,
            StrategyProperties properties) {
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
        final Strategy<@NonNull Goal> strategy = getStrategy(strategyName, proof, p);

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
     * A single entry of the preset combo box: either the built-in "Defaults", one of the profile's
     * further built-in presets, or a user-defined preset. User-defined entries can be deleted and
     * renamed; built-in entries cannot.
     */
    private static final class PresetEntry {
        private final String name;
        private final boolean userDefined;
        private final int maxSteps;
        private final Supplier<StrategyProperties> properties;

        private PresetEntry(String name, boolean userDefined, int maxSteps,
                Supplier<StrategyProperties> properties) {
            this.name = name;
            this.userDefined = userDefined;
            this.maxSteps = maxSteps;
            this.properties = properties;
        }

        static PresetEntry defaults() {
            return new PresetEntry("Defaults", false, DEFINITION.getDefaultMaxRuleApplications(),
                () -> DEFINITION.getDefaultPropertiesFactory().createDefaultStrategyProperties());
        }

        static PresetEntry builtIn(StrategySettingsDefinition.StrategySettingEntry e) {
            return new PresetEntry(e.name(), false, e.order(),
                () -> e.factory().createDefaultStrategyProperties());
        }

        static PresetEntry user(StrategyPreset preset) {
            return new PresetEntry(preset.name(), true, preset.maxSteps(), preset::properties);
        }

        String name() {
            return name;
        }

        boolean userDefined() {
            return userDefined;
        }

        int maxSteps() {
            return maxSteps;
        }

        StrategyProperties properties() {
            return properties.get();
        }

        @Override
        public String toString() {
            return name;
        }
    }

    /**
     * Renders the preset combo box rows. User-defined rows show a trailing "x" delete affordance,
     * and a separator line marks the transition from the built-in presets to the user-defined ones.
     */
    private final class PresetListCellRenderer implements ListCellRenderer<PresetEntry> {
        private final JPanel panel = new JPanel(new BorderLayout());
        private final JLabel nameLabel = new JLabel();
        private final JLabel deleteLabel = new JLabel("✕", SwingConstants.CENTER);

        PresetListCellRenderer() {
            panel.setOpaque(true);
            nameLabel.setOpaque(false);
            nameLabel.setBorder(BorderFactory.createEmptyBorder(2, 8, 2, 4));
            deleteLabel.setOpaque(false);
            panel.add(nameLabel, BorderLayout.CENTER);
            panel.add(deleteLabel, BorderLayout.EAST);
        }

        @Override
        public Component getListCellRendererComponent(JList<? extends PresetEntry> list,
                PresetEntry value, int index, boolean isSelected, boolean cellHasFocus) {
            Color bg = isSelected ? list.getSelectionBackground() : list.getBackground();
            Color fg = isSelected ? list.getSelectionForeground() : list.getForeground();
            panel.setBackground(bg);
            nameLabel.setFont(list.getFont());
            nameLabel.setForeground(fg);
            nameLabel.setText(value == null ? "" : value.name());

            boolean showDelete = value != null && value.userDefined() && index >= 0;
            deleteLabel.setPreferredSize(
                new Dimension(showDelete ? PRESET_DELETE_ZONE_WIDTH : 0, 0));
            if (showDelete) {
                deleteLabel.setText("✕");
                deleteLabel.setFont(list.getFont());
                boolean rollover = index == presetDeleteRolloverIndex;
                deleteLabel.setForeground(
                    rollover ? PRESET_DELETE_ACTIVE_COLOR : blend(fg, bg, 0.45f));
            } else {
                deleteLabel.setText("");
            }

            boolean separator = false;
            if (index > 0 && value != null && value.userDefined()) {
                Object prev = list.getModel().getElementAt(index - 1);
                separator = (prev instanceof PresetEntry pe) && !pe.userDefined();
            }
            Color sepColor = UIManager.getColor("Separator.foreground");
            if (sepColor == null) {
                sepColor = blend(fg, bg, 0.6f);
            }
            panel.setBorder(
                separator ? BorderFactory.createMatteBorder(1, 0, 0, 0, sepColor) : null);
            return panel;
        }
    }

    private static Color blend(Color a, Color b, float ratioB) {
        float ratioA = 1f - ratioB;
        return new Color(
            Math.round(a.getRed() * ratioA + b.getRed() * ratioB),
            Math.round(a.getGreen() * ratioA + b.getGreen() * ratioB),
            Math.round(a.getBlue() * ratioA + b.getBlue() * ratioB));
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
        private JComboBox<PresetEntry> strategyPredefSettingsCmb;

        /**
         * The menu button offering save / stash / rename actions for presets.
         */
        private JButton presetMenuButton;

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
        public JComboBox<PresetEntry> getStrategyPredefSettingsCmb() {
            return strategyPredefSettingsCmb;
        }

        /**
         * Sets the {@link JComboBox} for choosing a predefined value set.
         *
         * @param strategyPredefSettingsCmb The {@link JComboBox} for choosing a predefined value
         *        set.
         */
        public void setPredefsChoiceCmb(JComboBox<PresetEntry> strategyPredefSettingsCmb) {
            this.strategyPredefSettingsCmb = strategyPredefSettingsCmb;
        }

        /**
         * @return the menu button offering save / stash / rename actions
         */
        public JButton getPresetMenuButton() {
            return presetMenuButton;
        }

        /**
         * Sets the menu button offering save / stash / rename actions.
         *
         * @param presetMenuButton the menu button
         */
        public void setPresetMenuButton(JButton presetMenuButton) {
            this.presetMenuButton = presetMenuButton;
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
