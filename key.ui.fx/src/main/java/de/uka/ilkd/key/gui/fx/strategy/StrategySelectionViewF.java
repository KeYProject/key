/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.strategy;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.control.Label;
import javafx.scene.control.RadioButton;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.Spinner;
import javafx.scene.control.Toggle;
import javafx.scene.control.ToggleGroup;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.FlowPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Pane;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;

import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.core.fx.KeYSelectionModel;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.settings.StrategySettings;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.strategy.definition.AbstractStrategyPropertyDefinition;
import de.uka.ilkd.key.strategy.definition.OneOfStrategyPropertyDefinition;
import de.uka.ilkd.key.strategy.definition.StrategyPropertyValueDefinition;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;

import org.key_project.util.javafx.FxUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * First JavaFX version of the strategy selection view, the counter-part of
 * {@code de.uka.ilkd.key.gui.StrategySelectionView} (a Swing {@code JPanel}) in the module
 * {@code key.ui}.
 * <p>
 * <b>Milestone M2, first version.</b> Like the original, the widgets are generated from the
 * {@link StrategySettingsDefinition} of {@link JavaProfile#getDefault()}: every
 * {@link OneOfStrategyPropertyDefinition} becomes a {@link ToggleGroup} of {@link RadioButton}s
 * (the Swing view renders button groups, not a list of strategy factories), and the maximum
 * number of rule applications ({@code MaxRuleAppSlider} in the original) is edited by an
 * editable {@link Spinner} writing through to {@link StrategySettings#getMaxSteps()}.
 * <p>
 * All changes write through to the live settings exactly as the Swing view does: the values
 * shown by the widgets are overlaid on the active {@link StrategyProperties} of the selected
 * proof and stored both in the global {@code ProofSettings.DEFAULT_SETTINGS} and in the proof's
 * own settings, and the active strategy of the proof is recreated from the
 * {@link StrategyFactory} matching the proof's active strategy name (falling back to the
 * profile's default factory), mirroring the original's {@code updateStrategySettings} and
 * {@code KeYMediator#setMaxAutomaticSteps(int)}. The maximum steps are written to both settings
 * objects, like the mediator does.
 * <p>
 * The view observes a {@link KeYSelectionModel} ({@link #attach(KeYSelectionModel)}) and re-reads
 * the settings of the selected proof on every proof change ({@code refresh} of the original).
 * A programmatic-update guard ({@code updating}) prevents feedback loops while the widgets are
 * refreshed from the settings.
 * <p>
 * <b>Style classes</b> (styled in {@code key-light.css}/{@code key-dark.css}):
 * {@code .strategy-view} (this scroll pane), {@code .strategy-content} (inner VBox),
 * {@code .strategy-maxsteps-row}, {@code .strategy-maxsteps-label},
 * {@code .strategy-maxsteps-spinner}, {@code .strategy-section-title},
 * {@code .strategy-property-label}, {@code .strategy-property-values} (FlowPane of the buttons),
 * {@code .strategy-radio} (per value button), {@code .strategy-subproperty-row} and
 * {@code .strategy-status} (driver status label, not part of this view).
 * <p>
 * Deliberately deferred: the strategy preset combo box (built-in and user-defined presets with
 * save/stash/rename), the parallel-prover merge lock, the auto-prove "go" button, keyboard
 * shortcuts and the timeout setting (not shown by the Swing view either).
 */
public class StrategySelectionViewF extends ScrollPane {

    private static final Logger LOGGER = LoggerFactory.getLogger(StrategySelectionViewF.class);

    /**
     * Upper bound of the max-steps spinner. The Swing slider spans 1 to 9,000,000 in log steps; a
     * linear editable spinner covers the same range (the default is 10,000).
     */
    private static final int MAX_STEPS_BOUND = 10_000_000;

    /**
     * The max-steps value written through by {@link #verifyStrategyView()} (any in-bounds value
     * unlikely to equal the live settings).
     */
    private static final int VERIFY_MAX_STEPS = 4321;

    /**
     * The always used {@link StrategyFactory} of the fixed widget definition, mirroring
     * {@code StrategySelectionView.FACTORY}.
     */
    private static final StrategyFactory FACTORY = JavaProfile.getDefault();

    /**
     * The {@link StrategySettingsDefinition} of {@link #FACTORY} which defines the UI controls to
     * show, mirroring {@code StrategySelectionView.DEFINITION}.
     */
    private static final StrategySettingsDefinition DEFINITION = FACTORY.getSettingsDefinition();

    private final VBox content = new VBox();

    /**
     * Edits {@link StrategySettings#getMaxSteps()} ("Max. Rule Applications"), the
     * {@code MaxRuleAppSlider} of the Swing view.
     */
    private final Spinner<Integer> maxStepsSpinner = new Spinner<>(1, MAX_STEPS_BOUND, 10_000, 100);

    /**
     * Maps a strategy property key to the {@link ToggleGroup} which defines the value, mirroring
     * {@code StrategySelectionComponents.propertyGroups}.
     */
    private final Map<String, ToggleGroup> propertyGroups = new LinkedHashMap<>();

    /**
     * Maps a strategy property key to the {@link RadioButton}s which define the values, mirroring
     * {@code StrategySelectionComponents.propertyButtons}. The user data of each button is the
     * API value ({@code StrategyPropertyValueDefinition.getApiValue()}).
     */
    private final Map<String, List<RadioButton>> propertyButtons = new LinkedHashMap<>();

    private KeYSelectionModel selectionModel;
    private Proof proof;

    /**
     * Set while the widgets are updated programmatically from the settings ({@link #refresh}).
     * Guards the widget listeners so that they do not write the freshly read values back and
     * loop.
     */
    private boolean updating;

    private final KeYSelectionListener selectionListener = new KeYSelectionListener() {
        @Override
        public void selectedProofChanged(KeYSelectionEvent<Proof> event) {
            refresh(event.getSource().getSelectedProof());
        }
    };

    /**
     * Creates an empty strategy view; all controls are disabled until a proof is attached.
     */
    public StrategySelectionViewF() {
        getStyleClass().add("strategy-view");
        setFitToWidth(true);
        content.getStyleClass().add("strategy-content");
        content.setPadding(new Insets(8));
        content.setSpacing(6);
        setContent(content);

        // "Max. Rule Applications": label + spinner, the MaxRuleAppSlider of the Swing view
        Label maxStepsLabel = new Label(DEFINITION.getMaxRuleApplicationsLabel());
        maxStepsLabel.getStyleClass().add("strategy-maxsteps-label");
        maxStepsSpinner.getStyleClass().add("strategy-maxsteps-spinner");
        maxStepsSpinner.setEditable(true);
        maxStepsSpinner.valueProperty()
                .addListener((obs, oldValue, newValue) -> handleMaxStepsChange());
        HBox maxStepsRow = new HBox(8, maxStepsLabel, maxStepsSpinner);
        maxStepsRow.getStyleClass().add("strategy-maxsteps-row");
        maxStepsRow.setAlignment(Pos.CENTER_LEFT);
        content.getChildren().add(maxStepsRow);

        // Generated strategy property groups ("JavaDL Options")
        if (!DEFINITION.getProperties().isEmpty()) {
            Label title = new Label(DEFINITION.getPropertiesTitle());
            title.getStyleClass().add("strategy-section-title");
            content.getChildren().add(title);
            for (AbstractStrategyPropertyDefinition definition : DEFINITION.getProperties()) {
                addPropertyControls(content, definition, true);
            }
        }

        enableAll(false);
    }

    /**
     * Registers this view as a selection listener on the given model and shows the settings of
     * the currently selected proof, if any.
     *
     * @param model the selection model to observe
     */
    public void attach(KeYSelectionModel model) {
        Objects.requireNonNull(model);
        if (selectionModel == model) {
            return;
        }
        if (selectionModel != null) {
            selectionModel.removeKeYSelectionListener(selectionListener);
        }
        selectionModel = model;
        model.addKeYSelectionListenerChecked(selectionListener);
        refresh(model.getSelectedProof());
    }

    /**
     * Shows the strategy settings of the given proof, the counter-part of
     * {@code StrategySelectionView.refresh(Proof)}: the radio buttons reflect the proof's active
     * strategy properties and the spinner its maximum steps.
     *
     * @param newProof the proof whose settings are displayed, may be {@code null}
     */
    public void refresh(Proof newProof) {
        if (!FxUtil.isFxThread()) {
            FxUtil.runLater(() -> refresh(newProof));
            return;
        }
        proof = newProof;
        if (proof == null) {
            enableAll(false);
            return;
        }
        updating = true;
        try {
            StrategySettings settings = proof.getSettings().getStrategySettings();
            StrategyProperties active = settings.getActiveStrategyProperties();
            for (Map.Entry<String, List<RadioButton>> entry : propertyButtons.entrySet()) {
                String value = active.getProperty(entry.getKey());
                for (RadioButton button : entry.getValue()) {
                    button.setSelected(Objects.equals(button.getUserData(), value));
                }
            }
            int steps =
                Math.clamp(settings.getMaxSteps(), 1, MAX_STEPS_BOUND);
            maxStepsSpinner.getValueFactory().setValue(steps);
            enableAll(true);
        } finally {
            updating = false;
        }
    }

    /**
     * @return the proof whose settings are displayed, or {@code null} if none is attached
     */
    public Proof getProof() {
        return proof;
    }

    /**
     * Enables or disables all controls, mirroring {@code StrategySelectionView.enableAll}.
     *
     * @param enable {@code true} to enable the controls
     */
    private void enableAll(boolean enable) {
        content.setDisable(!enable);
    }

    /**
     * Adds the UI controls of the given strategy property definition (a radio button group), the
     * JavaFX counter-part of {@code StrategySelectionView.createStrategyProperty}. Sub-properties
     * are rendered after their parent, indented and with the label inline, like the original.
     *
     * @param parent the container to append to
     * @param definition the property definition to render
     * @param topLevel whether the label is rendered on its own line above the buttons
     */
    private void addPropertyControls(Pane parent, AbstractStrategyPropertyDefinition definition,
            boolean topLevel) {
        if (!(definition instanceof OneOfStrategyPropertyDefinition oneOf)) {
            LOGGER.warn("Unsupported strategy property definition: {}", definition);
            return;
        }
        Label label = new Label(oneOf.getName());
        label.getStyleClass().add("strategy-property-label");
        if (oneOf.getTooltip() != null) {
            label.setTooltip(new Tooltip(oneOf.getTooltip()));
        }
        ToggleGroup group = new ToggleGroup();
        FlowPane values = new FlowPane();
        values.getStyleClass().add("strategy-property-values");
        values.setHgap(10);
        values.setVgap(2);
        if (!oneOf.getValues().isEmpty()) {
            propertyGroups.put(oneOf.getApiKey(), group);
            group.selectedToggleProperty().addListener((obs, oldToggle, newToggle) -> {
                if (newToggle != null) {
                    handleStrategyChange();
                }
            });
            for (StrategyPropertyValueDefinition valueDefinition : oneOf.getValues()) {
                RadioButton button = new RadioButton(valueDefinition.getValue());
                button.getStyleClass().add("strategy-radio");
                button.setToggleGroup(group);
                button.setUserData(valueDefinition.getApiValue());
                if (valueDefinition.getTooltip() != null) {
                    button.setTooltip(new Tooltip(valueDefinition.getTooltip()));
                }
                propertyButtons.computeIfAbsent(oneOf.getApiKey(), k -> new ArrayList<>())
                        .add(button);
                values.getChildren().add(button);
            }
        }
        if (topLevel) {
            parent.getChildren().add(label);
            parent.getChildren().add(values);
        } else {
            HBox row = new HBox(8, label, values);
            row.getStyleClass().add("strategy-subproperty-row");
            row.setPadding(new Insets(0, 0, 0, 16));
            row.setAlignment(Pos.CENTER_LEFT);
            HBox.setHgrow(values, Priority.ALWAYS);
            parent.getChildren().add(row);
        }
        for (AbstractStrategyPropertyDefinition subProperty : definition.getSubProperties()) {
            addPropertyControls(parent, subProperty, false);
        }
    }

    /**
     * Called when the user edits the max-steps spinner: writes the new value to the settings of
     * the selected proof and to the global default settings, mirroring
     * {@code KeYMediator.setMaxAutomaticSteps(int)}.
     */
    private void handleMaxStepsChange() {
        if (updating) {
            return;
        }
        Integer steps = maxStepsSpinner.getValue();
        if (steps == null) {
            return;
        }
        LOGGER.debug("Maximum rule applications changed to {}", steps);
        if (proof != null) {
            proof.getSettings().getStrategySettings().setMaxSteps(steps);
        }
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(steps);
    }

    /**
     * Called when the user selects a strategy property value: updates the strategy settings of
     * the selected proof, mirroring the action listener of the Swing radio buttons.
     */
    private void handleStrategyChange() {
        if (updating || proof == null) {
            return;
        }
        updateStrategySettings();
    }

    /**
     * Writes the values shown by the widgets through to the live strategy settings: the displayed
     * properties are overlaid on the proof's active properties and stored in the global default
     * settings as well as in the proof's settings, and the active strategy is recreated from the
     * matching {@link StrategyFactory} (mirroring {@code StrategySelectionView
     * #updateStrategySettings(String, StrategyProperties)}).
     */
    private void updateStrategySettings() {
        StrategyProperties properties = currentStrategyProperties();
        Strategy<Goal> strategy =
            getStrategy(proof.getActiveStrategy().name().toString(), properties);
        LOGGER.debug("Writing strategy settings through ({} properties)", properties.size());
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setStrategy(strategy.name());
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings()
                .setActiveStrategyProperties(properties);
        proof.getSettings().getStrategySettings().setStrategy(strategy.name());
        proof.getSettings().getStrategySettings().setActiveStrategyProperties(properties);
        proof.setActiveStrategy(strategy);
    }

    /**
     * Captures the strategy properties currently reflected by the widgets: starts from the
     * complete active properties of the proof and overlays the values shown by the radio groups,
     * so that properties without a control keep their value (mirroring
     * {@code StrategySelectionView.currentStrategyProperties}).
     *
     * @return the merged properties
     */
    private StrategyProperties currentStrategyProperties() {
        StrategyProperties base =
            proof.getSettings().getStrategySettings().getActiveStrategyProperties();
        StrategyProperties displayed = getDisplayedProperties();
        for (String key : displayed.stringPropertyNames()) {
            base.setProperty(key, displayed.getProperty(key));
        }
        return base;
    }

    /**
     * Builds the strategy properties reflected by the radio groups; a group without a selection
     * falls back to the default value of the settings definition, mirroring
     * {@code StrategySelectionView.getProperties()}.
     *
     * @return the displayed properties
     */
    private StrategyProperties getDisplayedProperties() {
        StrategyProperties properties = new StrategyProperties();
        for (Map.Entry<String, ToggleGroup> entry : propertyGroups.entrySet()) {
            Toggle selected = entry.getValue().getSelectedToggle();
            if (selected != null) {
                properties.setProperty(entry.getKey(), (String) selected.getUserData());
            } else {
                properties.setProperty(entry.getKey(),
                    DEFINITION.getDefaultPropertiesFactory().createDefaultStrategyProperties()
                            .getProperty(entry.getKey()));
            }
        }
        return properties;
    }

    /**
     * Creates the strategy of the given name from the given properties, using the supported
     * {@link StrategyFactory}s of the selected proof's profile and falling back to the profile's
     * default factory (mirroring {@code StrategySelectionView.getStrategy}).
     *
     * @param strategyName the name of the strategy to create
     * @param properties the strategy properties to configure the strategy with
     * @return the strategy instance
     */
    private Strategy<Goal> getStrategy(String strategyName, StrategyProperties properties) {
        Profile profile = proof.getServices().getProfile();
        for (StrategyFactory factory : profile.supportedStrategies()) {
            if (strategyName.equals(factory.name().toString())) {
                return factory.create(proof, properties);
            }
        }
        LOGGER.info("Selected Strategy '{}' not found falling back to {}", strategyName,
            profile.getDefaultStrategyFactory().name());
        return profile.getDefaultStrategyFactory().create(proof, properties);
    }

    /**
     * Development self-test (M2): verifies that the widgets were generated completely from the
     * settings definition (one radio group per one-of property, including sub-properties) and
     * that edits write through to the live settings objects: the maximum steps are driven through
     * the spinner widget and read back from both the proof's and the global settings, and one
     * radio group is toggled through the widget and read back from the proof's strategy
     * properties. The original values are restored afterwards.
     *
     * @return a one-line report, {@code "... PASS"} if everything is consistent
     */
    public String verifyStrategyView() {
        if (!FxUtil.isFxThread()) {
            return FxUtil.callAndWait(this::verifyStrategyView);
        }
        if (proof == null) {
            return "no proof";
        }
        int expectedGroups = 0;
        for (AbstractStrategyPropertyDefinition definition : DEFINITION.getProperties()) {
            expectedGroups += countOneOfDefinitions(definition);
        }
        int renderedGroups = propertyGroups.size();
        int renderedRadios = propertyButtons.values().stream().mapToInt(List::size).sum();

        // write-through check: max steps via the spinner widget
        StrategySettings settings = proof.getSettings().getStrategySettings();
        int originalSteps = settings.getMaxSteps();
        int probeSteps =
            originalSteps == VERIFY_MAX_STEPS ? VERIFY_MAX_STEPS + 1 : VERIFY_MAX_STEPS;
        maxStepsSpinner.getValueFactory().setValue(probeSteps);
        int writtenSteps = settings.getMaxSteps();
        int globalSteps = ProofSettings.DEFAULT_SETTINGS.getStrategySettings().getMaxSteps();
        maxStepsSpinner.getValueFactory().setValue(originalSteps);
        int restoredSteps = settings.getMaxSteps();

        // write-through check: one radio group via the widget
        RadioProbe probe = findRadioProbe();
        String radioReport = "skipped";
        boolean radioOk = true;
        if (probe != null) {
            String before = settings.getActiveStrategyProperty(probe.key());
            probe.alternative().setSelected(true);
            String after = settings.getActiveStrategyProperty(probe.key());
            probe.current().setSelected(true);
            String restored = settings.getActiveStrategyProperty(probe.key());
            radioReport = probe.key() + ":" + before + "->" + after + "->" + restored;
            radioOk = Objects.equals(after, probe.alternative().getUserData())
                    && Objects.equals(restored, before);
        }

        boolean pass = renderedGroups == expectedGroups && renderedRadios > 0
                && writtenSteps == probeSteps && globalSteps == probeSteps
                && restoredSteps == originalSteps && radioOk;
        return "groups=" + renderedGroups + "/" + expectedGroups + " radios=" + renderedRadios
            + " maxSteps=" + originalSteps + "->" + probeSteps + "->" + writtenSteps + "->"
            + restoredSteps + " radio[" + radioReport + "] " + (pass ? "PASS" : "FAIL");
    }

    /**
     * Counts the given definition and its sub-definitions which are one-of property definitions
     * with at least one value; the expected number of rendered radio groups (the Swing original
     * skips empty definitions as well, see {@code createStrategyProperty}).
     *
     * @param definition the definition to count, together with its sub-properties
     * @return the number of rendered one-of definitions
     */
    private static int countOneOfDefinitions(AbstractStrategyPropertyDefinition definition) {
        int count = 0;
        if (definition instanceof OneOfStrategyPropertyDefinition oneOf
                && !oneOf.getValues().isEmpty()) {
            count = 1;
        }
        for (AbstractStrategyPropertyDefinition subProperty : definition.getSubProperties()) {
            count += countOneOfDefinitions(subProperty);
        }
        return count;
    }

    /**
     * Finds a radio group suitable for the write-through probe: at least two buttons where the
     * currently active property value of the proof matches one of the buttons (the one to
     * restore).
     *
     * @return the probe, or {@code null} if no group qualifies
     */
    private RadioProbe findRadioProbe() {
        StrategySettings settings = proof.getSettings().getStrategySettings();
        for (Map.Entry<String, List<RadioButton>> entry : propertyButtons.entrySet()) {
            if (entry.getValue().size() < 2) {
                continue;
            }
            String value = settings.getActiveStrategyProperty(entry.getKey());
            RadioButton current = null;
            RadioButton alternative = null;
            for (RadioButton button : entry.getValue()) {
                if (Objects.equals(button.getUserData(), value)) {
                    current = button;
                } else if (alternative == null) {
                    alternative = button;
                }
            }
            if (current != null && alternative != null) {
                return new RadioProbe(entry.getKey(), current, alternative);
            }
        }
        return null;
    }

    /**
     * A radio group probe of {@link #verifyStrategyView()}: the group key plus the button holding
     * the currently active value (restored after the probe) and another button (written through
     * during the probe).
     */
    private record RadioProbe(String key, RadioButton current, RadioButton alternative) {
    }
}
