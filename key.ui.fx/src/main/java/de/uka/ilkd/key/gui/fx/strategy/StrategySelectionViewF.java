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
import javafx.scene.control.Alert;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonType;
import javafx.scene.control.ComboBox;
import javafx.scene.control.ContentDisplay;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Label;
import javafx.scene.control.ListCell;
import javafx.scene.control.MenuItem;
import javafx.scene.control.RadioButton;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.Separator;
import javafx.scene.control.SeparatorMenuItem;
import javafx.scene.control.Slider;
import javafx.scene.control.Spinner;
import javafx.scene.control.TextInputDialog;
import javafx.scene.control.Toggle;
import javafx.scene.control.ToggleGroup;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.FlowPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Pane;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.core.fx.KeYSelectionModel;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.settings.StrategyPresetsSettings;
import de.uka.ilkd.key.settings.StrategyPresetsSettings.StrategyPreset;
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
 * {@code .strategy-radio} (per value button), {@code .strategy-subproperty-row},
 * {@code .strategy-preset-row}, {@code .strategy-preset-combo}, {@code .strategy-preset-menu},
 * {@code .strategy-preset-apply} and
 * {@code .strategy-status} (driver status label, not part of this view).
 * <p>
 * WP-3 (goallist-strategy-info parity): the strategy preset combo box is ported (Swing
 * {@code StrategySelectionView.createDefaultPanel}, StrategySelectionView.java:456-499): the row
 * {@code [gear] [combo] [Apply]} mirrors the Swing layout — the combo lists the built-in
 * "Defaults" entry, the further built-in presets of the settings definition and the user-defined
 * presets of {@link StrategyPresetsSettings} (user rows carry a trailing "✕" delete affordance
 * like the Swing {@code PresetListCellRenderer}); selecting an entry applies it immediately, the
 * Apply button re-applies the current selection and is disabled until the next widget edit
 * (Swing {@code predefChanged}/{@code refreshDefaultButton}); the gear button offers
 * "Save current as…", "Stash current" and "Rename selected…" (Swing {@code showPresetMenu},
 * StrategySelectionView.java:635-661). Applying a preset writes the preset's maximum rule
 * applications to the proof's strategy settings and its properties through
 * {@link #updateStrategySettings} (Swing {@code applySelectedPreset},
 * StrategySelectionView.java:572-585).
 * <p>
 * Deliberately deferred: the timeout setting (not shown by the Swing view either). The
 * parallel-prover merge lock and the auto-prove "go" button are implemented (strategy markers).
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
     * strategy: the "Go"/"Stop" button (Swing {@code StrategySelectionView.btnGo}, a plain
     * button carrying the shared {@code AutoModeAction}, StrategySelectionView.java:157-208):
     * starts the automatic proof search of the selected proof, or stops a running one. The label
     * follows the auto mode via {@link KeYMediatorF#autoModeRunningProperty()} (Swing
     * {@code AutoModeAction.autoModeStarted/autoModeStopped}, AutoModeAction.java:109-138).
     */
    private final Button goButton = new Button("Go");

    /**
     * WP-3 (goallist-strategy-info): the preset combo box (Swing
     * {@code components.strategyPredefSettingsCmb}, StrategySelectionView.java:464-466): the
     * built-in "Defaults" entry, the further built-in presets of the settings definition and the
     * user-defined presets of {@link StrategyPresetsSettings}. Selecting an entry applies it
     * immediately (Swing combo box action listener, StrategySelectionView.java:474-478).
     */
    private final ComboBox<PresetEntry> presetCombo = new ComboBox<>();

    /**
     * WP-3: the gear button beside the combo (Swing {@code createPresetMenuButton},
     * StrategySelectionView.java:625-633): offers "Save current as…", "Stash current" and
     * "Rename selected…".
     */
    private final Button presetMenuButton = new Button("⚙");

    /**
     * WP-3: the Apply button (Swing {@code defaultButton}, StrategySelectionView.java:459-462):
     * re-applies the preset currently selected in the combo; disabled until the next widget edit
     * after an application (Swing {@code predefChanged}/{@code refreshDefaultButton},
     * StrategySelectionView.java:104/897-907).
     */
    private final Button applyButton = new Button("Apply");

    /**
     * WP-3: whether a chosen preset has been changed by a widget edit since; gates the Apply
     * button enablement (Swing {@code predefChanged}, StrategySelectionView.java:100-104).
     */
    private boolean predefChanged = true;

    /**
     * Set only while {@link #verifyPresetCombo()} runs: the headless verify drives the
     * parameterized core methods directly, so the modal alerts (built-in-name warning, overwrite
     * confirmation) are suppressed — a {@code showAndWait()} with nobody to click would hang the
     * app run.
     */
    private boolean verifyRun;

    /**
     * WP-3: set while the preset combo is rebuilt or reselected programmatically; guards the
     * combo's action listener so it does not (re-)apply a preset in reaction to our own changes
     * (Swing {@code adjustingPresetCombo}, StrategySelectionView.java:106-110).
     */
    private boolean adjustingPresetCombo;

    /**
     * Edits {@link StrategySettings#getMaxSteps()} ("Max. Rule Applications"), the
     * {@code MaxRuleAppSlider} of the Swing view.
     */
    private final Spinner<Integer> maxStepsSpinner = new Spinner<>(1, MAX_STEPS_BOUND, 10_000, 100);

    /**
     * The logarithmic max-steps slider, the FX counterpart of the Swing
     * {@code MaxRuleAppSlider} (reviewer request): position p maps to the value
     * {@code (p % 9 + 1) * 10^(p / 9)}, i.e. one decade every 9 units, and it is kept in sync
     * with the {@link #maxStepsSpinner}.
     */
    private final Slider maxStepsSlider = new Slider();

    /** One decade per 9 slider units, the Swing {@code MaxRuleAppSlider.MAX_RULE_APPS_LOG10}. */
    private static final int MAX_RULE_APPS_LOG10 = 6;

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
     * strategy: the shared mediator (via {@link #attachMediator}), driving the {@link #goButton};
     * {@code null} until attached (the button stays disabled).
     */
    private KeYMediatorF mediator;

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

        // strategy: the Go/Stop button row (Swing btnGo, StrategySelectionView.java:207-208/179)
        goButton.getStyleClass().add("strategy-go");
        goButton.setTooltip(new Tooltip("Start or stop the automatic proof search"));
        goButton.setDisable(true);
        goButton.setOnAction(e -> handleGoButton());
        HBox goRow = new HBox(8, goButton);
        goRow.getStyleClass().add("strategy-go-row");
        goRow.setAlignment(Pos.CENTER_LEFT);
        content.getChildren().add(goRow);

        // WP-3: the preset row [gear][combo][Apply] (Swing createDefaultPanel,
        // StrategySelectionView.java:456-499 — the row layout "presetMenuButton, combo,
        // defaultButton" of the original)
        presetMenuButton.getStyleClass().add("strategy-preset-menu");
        presetMenuButton.setTooltip(new Tooltip("Save, stash or rename presets"));
        presetMenuButton.setDisable(true);
        presetMenuButton.setOnAction(e -> showPresetMenu());
        presetCombo.getStyleClass().add("strategy-preset-combo");
        presetCombo.setTooltip(new Tooltip("Predefined strategy settings"));
        presetCombo.setDisable(true);
        presetCombo.setCellFactory(lv -> new PresetCell());
        presetCombo.setButtonCell(new PresetCell());
        presetCombo.valueProperty().addListener((obs, old, entry) -> {
            if (!adjustingPresetCombo && entry != null) {
                applySelectedPreset();
            }
        });
        applyButton.getStyleClass().add("strategy-preset-apply");
        applyButton.setTooltip(new Tooltip("Apply the selected predefined settings"));
        applyButton.setDisable(true);
        applyButton.setOnAction(e -> applySelectedPreset());
        HBox presetRow = new HBox(8, presetMenuButton, presetCombo, applyButton);
        presetRow.getStyleClass().add("strategy-preset-row");
        presetRow.setAlignment(Pos.CENTER_LEFT);
        HBox.setHgrow(presetCombo, Priority.ALWAYS);
        content.getChildren().add(presetRow);
        rebuildPresetCombo(null);

        // "Max. Rule Applications": label + logarithmic slider + spinner, the FX counterpart
        // of the Swing MaxRuleAppSlider (reviewer request: a slider for selecting the maximum
        // number of rule applications). The slider position maps to the value like the Swing
        // original: pos p -> (p % 9 + 1) * 10^(p / 9), tick labels 1, 10, 100, 1k, ..., 1M.
        Label maxStepsLabel = new Label(DEFINITION.getMaxRuleApplicationsLabel());
        maxStepsLabel.getStyleClass().add("strategy-maxsteps-label");
        maxStepsSpinner.getStyleClass().add("strategy-maxsteps-spinner");
        maxStepsSpinner.setEditable(true);
        maxStepsSpinner.valueProperty()
                .addListener((obs, oldValue, newValue) -> handleMaxStepsChange());
        configureMaxStepsSlider();
        maxStepsSlider.valueProperty().addListener((obs, oldValue, newValue) -> {
            int pos = (int) Math.round(maxStepsSlider.getValue());
            int value = (pos % 9 + 1) * (int) Math.pow(10, pos / 9);
            Integer current = maxStepsSpinner.getValue();
            if (current == null || current != value) {
                // writes the settings via the spinner's change listener (Swing
                // MaxRuleAppSlider change listener -> mediator.setMaxAutomaticSteps)
                maxStepsSpinner.getValueFactory().setValue(value);
            }
        });
        maxStepsSpinner.valueProperty().addListener((obs, oldValue, newValue) -> {
            if (newValue != null) {
                maxStepsSlider.setValue(sliderPos(newValue));
            }
        });
        maxStepsSlider.setValue(sliderPos(maxStepsSpinner.getValue()));
        HBox maxStepsRow = new HBox(8, maxStepsLabel, maxStepsSlider, maxStepsSpinner);
        maxStepsRow.getStyleClass().add("strategy-maxsteps-row");
        maxStepsRow.setAlignment(Pos.CENTER_LEFT);
        HBox.setHgrow(maxStepsSlider, Priority.ALWAYS);
        content.getChildren().add(maxStepsRow);

        // Generated strategy property groups ("JavaDL Options")
        if (!DEFINITION.getProperties().isEmpty()) {
            // reviewer request: visual section separators between the setting groups (like the
            // section separators of the Swing view)
            content.getChildren().add(new Separator());
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
     * Configures the logarithmic max-steps slider (the Swing {@code MaxRuleAppSlider} setup:
     * range {@code [0, 54]}, one decade every 9 units, tick marks and the decade labels 1, 10,
     * 100, 1k, 10k, 100k, 1M).
     */
    private void configureMaxStepsSlider() {
        maxStepsSlider.getStyleClass().add("strategy-maxsteps-slider");
        maxStepsSlider.setMin(0);
        maxStepsSlider.setMax(MAX_RULE_APPS_LOG10 * 9);
        maxStepsSlider.setMajorTickUnit(9);
        maxStepsSlider.setMinorTickCount(8);
        maxStepsSlider.setShowTickMarks(true);
        maxStepsSlider.setShowTickLabels(true);
        maxStepsSlider.setSnapToTicks(false);
        maxStepsSlider.setLabelFormatter(new javafx.util.StringConverter<>() {
            @Override
            public String toString(Double pos) {
                int p = (int) Math.round(pos);
                int value = (p % 9 + 1) * (int) Math.pow(10, p / 9);
                return value >= 10000 ? value >= 1000000 ? (value / 1000000) + "M"
                        : (value / 1000) + "k" : String.valueOf(value);
            }

            @Override
            public Double fromString(String string) {
                return null;
            }
        });
    }

    /**
     * Maps a max-rule-applications value to the slider position (Swing
     * {@code MaxRuleAppSlider.setPos}).
     *
     * @param maxRuleApps the value, may be {@code null} (then 0)
     * @return the slider position in {@code [0, 54]}
     */
    private static int sliderPos(Integer maxRuleApps) {
        if (maxRuleApps == null || maxRuleApps <= 0) {
            return 0;
        }
        int major = (int) (Math.log(maxRuleApps) / Math.log(10));
        int minor = maxRuleApps / (int) Math.pow(10, major) - 1;
        return Math.max(0, Math.min(MAX_RULE_APPS_LOG10 * 9, major * 9 + minor));
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

    // strategy: begin — the Go/Stop button + the parallel-prover merge lock (Swing
    // StrategySelectionView.btnGo + reflectParallelProverMergeLock)
    /**
     * strategy: supplies the mediator driving the {@link #goButton} and registers the
     * parallel-prover merge-lock listener (Swing {@code StrategySelectionView} constructor
     * property-change listener, StrategySelectionView.java:161-165). Idempotent: re-attaching
     * the same mediator is a no-op.
     *
     * @param newMediator the shared mediator, may be {@code null} to detach
     */
    public void attachMediator(KeYMediatorF newMediator) {
        if (this.mediator == newMediator) {
            return;
        }
        this.mediator = newMediator;
        if (newMediator == null) {
            goButton.setDisable(true);
            goButton.setText("Go");
            return;
        }
        // the label follows the auto mode (Swing AutoModeAction.autoModeStarted/autoModeStopped,
        // AutoModeAction.java:109-138: "Stop" while running, "Start"/"Continue" otherwise)
        newMediator.autoModeRunningProperty().addListener(
            (obs, wasRunning, running) -> updateGoButton(running));
        updateGoButton(newMediator.autoModeRunningProperty().get());
        // the merge lock follows the parallel-prover toggle (the Swing view re-registers the
        // same property-change listener in its constructor)
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
                .addPropertyChangeListener(GeneralSettings.PARALLEL_PROVER_ENABLED,
                    evt -> reflectParallelProverMergeLock());
        reflectParallelProverMergeLock();
    }

    /**
     * strategy: the Go/Stop button action (Swing AutoModeAction.actionPerformed,
     * AutoModeAction.java:154-177): starts the automatic proof search of the selected proof, or
     * stops a running one. While auto mode runs the input freeze blocks the rest of the UI (the
     * Freeze of the Swing MainWindow) — the freeze keeps {@code Escape} (the Swing
     * {@code AutoModeAction.STOP_KEY}) live, which stops the run.
     */
    private void handleGoButton() {
        if (mediator == null) {
            return;
        }
        if (mediator.autoModeRunningProperty().get()) {
            mediator.stopAutoMode();
        } else {
            mediator.startAutoMode();
        }
    }

    /**
     * strategy: updates the Go/Stop button label (Swing AutoModeAction: "Stop" while the auto
     * mode runs, "Start"/"Continue" otherwise — the FX button always shows "Go" when idle).
     *
     * @param running whether the auto mode is running
     */
    private void updateGoButton(boolean running) {
        goButton.setText(running ? "Stop" : "Go");
        goButton.setTooltip(new Tooltip(running ? "Stop the automatic proof search"
                : "Start the automatic proof search"));
    }

    /**
     * strategy: reflects in the strategy view that the merge rule is unavailable while the
     * multi-core prover is active: the merge-point option group is forced to <em>skip</em> and
     * greyed with an explanatory tooltip (Swing
     * {@code StrategySelectionView.reflectParallelProverMergeLock},
     * StrategySelectionView.java:869-895). This is view-only — the stored strategy property is
     * left untouched, so the user's real choice reappears when they switch back to the
     * single-core prover (the merge rule is additionally disabled at the engine level during
     * parallel runs, {@code MergeRule.isApplicable}).
     */
    private void reflectParallelProverMergeLock() {
        boolean mt =
            ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
                    .isParallelProverEnabled();
        List<RadioButton> mergeButtons = propertyButtons.get(StrategyProperties.MPS_OPTIONS_KEY);
        if (mergeButtons == null) {
            return;
        }
        for (RadioButton button : mergeButtons) {
            if (mt) {
                button.setSelected(StrategyProperties.MPS_SKIP.equals(button.getUserData()));
                button.setDisable(true);
                button.setTooltip(new Tooltip("The merge rule is disabled while the multi-core "
                    + "prover is active (forced to 'skip'). Switch to the single-core prover "
                    + "to use it."));
            } else {
                button.setDisable(false);
                button.setTooltip(null);
            }
        }
    }
    // strategy: end

    // WP-3: begin — the strategy preset combo / stash UI (Swing StrategySelectionView.java
    // :456-499, :515-585, :592-750)

    /**
     * A single entry of the preset combo box: either the built-in "Defaults", one of the
     * profile's further built-in presets, or a user-defined preset (Swing {@code PresetEntry},
     * StrategySelectionView.java:1008-1061). User-defined entries can be deleted and renamed;
     * built-in entries cannot.
     */
    private static final class PresetEntry {

        private final boolean userDefined;
        private final StrategyPreset data;

        private PresetEntry(String name, boolean userDefined, int maxSteps,
                StrategyProperties properties) {
            this(userDefined, new StrategyPreset(name, maxSteps, properties));
        }

        private PresetEntry(boolean userDefined, StrategyPreset preset) {
            this.data = preset;
            this.userDefined = userDefined;
        }

        static PresetEntry defaults() {
            return new PresetEntry("Defaults", false, DEFINITION.getDefaultMaxRuleApplications(),
                DEFINITION.getDefaultPropertiesFactory().createDefaultStrategyProperties());
        }

        static PresetEntry builtIn(StrategySettingsDefinition.StrategySettingEntry e) {
            return new PresetEntry(e.name(), false, e.order(),
                e.factory().createDefaultStrategyProperties());
        }

        static PresetEntry user(StrategyPreset preset) {
            return new PresetEntry(true, preset);
        }

        String name() {
            return data.name();
        }

        boolean userDefined() {
            return userDefined;
        }

        int maxSteps() {
            return data.maxSteps();
        }

        StrategyProperties properties() {
            return data.properties();
        }

        @Override
        public String toString() {
            return data.name();
        }
    }

    /**
     * Renders the preset combo box rows (Swing {@code PresetListCellRenderer},
     * StrategySelectionView.java:1063-1105): user-defined rows show a trailing "✕" delete
     * affordance; built-in rows only the name.
     */
    private final class PresetCell extends ListCell<PresetEntry> {
        private final Label nameLabel = new Label();
        private final Label deleteLabel = new Label("✕");

        PresetCell() {
            HBox box = new HBox(6, nameLabel, deleteLabel);
            box.setAlignment(Pos.CENTER_LEFT);
            nameLabel.setMaxWidth(Double.MAX_VALUE);
            HBox.setHgrow(nameLabel, Priority.ALWAYS);
            deleteLabel.getStyleClass().add("strategy-preset-delete");
            deleteLabel.setTooltip(new Tooltip("Delete this preset"));
            deleteLabel.setOnMouseClicked(e -> {
                if (getItem() != null && getItem().userDefined()) {
                    deleteUserPreset(getItem());
                    e.consume();
                }
            });
            setContentDisplay(ContentDisplay.GRAPHIC_ONLY);
            setGraphic(box);
        }

        @Override
        protected void updateItem(PresetEntry item, boolean empty) {
            super.updateItem(item, empty);
            nameLabel.setText(empty || item == null ? "" : item.name());
            boolean showDelete = !empty && item != null && item.userDefined();
            deleteLabel.setVisible(showDelete);
            deleteLabel.setManaged(showDelete);
        }
    }

    /**
     * @return the proof-independent settings storing the user-defined strategy presets (Swing
     *         {@code getPresetsSettings}, StrategySelectionView.java:515-517)
     */
    private static StrategyPresetsSettings getPresetsSettings() {
        return ProofIndependentSettings.DEFAULT_INSTANCE.getStrategyPresetsSettings();
    }

    /**
     * Builds the list of combo box entries: the built-in "Defaults", the further built-in
     * presets defined by the profile, followed by the user-defined presets (Swing
     * {@code buildPresetEntries}, StrategySelectionView.java:523-533).
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
     * Rebuilds the preset combo model from the built-in and stored presets without touching the
     * live strategy settings (Swing {@code rebuildPresetCombo},
     * StrategySelectionView.java:542-567).
     *
     * @param selectName the name of the preset to select afterwards, or {@code null} to select
     *        the first entry ("Defaults")
     */
    private void rebuildPresetCombo(String selectName) {
        List<PresetEntry> entries = buildPresetEntries();
        adjustingPresetCombo = true;
        try {
            presetCombo.getItems().setAll(entries);
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
            presetCombo.getSelectionModel().select(toSelect);
        } finally {
            adjustingPresetCombo = false;
        }
    }

    /**
     * Applies the preset currently selected in the combo box to the active proof (Swing
     * {@code applySelectedPreset}, StrategySelectionView.java:572-585): the preset's maximum
     * rule applications are written to the proof's strategy settings, the preset's properties
     * become the active strategy, and the Apply button is disabled until the next widget edit.
     */
    private void applySelectedPreset() {
        if (proof == null) {
            return;
        }
        PresetEntry entry = presetCombo.getValue();
        if (entry == null) {
            return;
        }
        proof.getSettings().getStrategySettings().setMaxSteps(entry.maxSteps());
        predefChanged = false;
        updateStrategySettings(FACTORY.name().toString(), entry.properties());
        refresh(proof);
    }

    /**
     * @param name a candidate preset name
     * @return {@code true} if the name is used by a built-in preset (and thus reserved) (Swing
     *         {@code isBuiltInName}, StrategySelectionView.java:613-623)
     */
    private static boolean isBuiltInName(String name) {
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

    /**
     * Shows the gear menu (Swing {@code showPresetMenu}, StrategySelectionView.java:635-661):
     * "Save current as…", "Stash current", separator, "Rename selected…" (enabled only for
     * user-defined entries). The dialogs collect the name and then delegate to the parameterized
     * core methods, which the headless {@code key.fx.verify.goallist} assertions drive directly.
     */
    private void showPresetMenu() {
        PresetEntry selected = presetCombo.getValue();
        ContextMenu menu = new ContextMenu();
        MenuItem saveAs = new MenuItem("Save current as…");
        saveAs.setOnAction(e -> {
            TextInputDialog dialog = new TextInputDialog("");
            dialog.setTitle("Save strategy preset");
            dialog.setHeaderText("Preset name:");
            String input = dialog.showAndWait().orElse(null);
            saveCurrentAs(input);
        });
        MenuItem stash = new MenuItem("Stash current");
        stash.setOnAction(e -> stashCurrent());
        MenuItem rename = new MenuItem("Rename selected…");
        rename.disableProperty().set(selected == null || !selected.userDefined());
        rename.setOnAction(e -> {
            TextInputDialog dialog = new TextInputDialog(
                selected == null ? "" : selected.name());
            dialog.setTitle("Rename strategy preset");
            dialog.setHeaderText("New name:");
            String input = dialog.showAndWait().orElse(null);
            renameSelected(input);
        });
        menu.getItems().addAll(saveAs, stash, new SeparatorMenuItem(), rename);
        // reviewer request (bug): the menu opened at screen coordinates (0, buttonHeight) —
        // i.e. the left top corner of the desktop (PopupWindow.show(Node, x, y) expects SCREEN
        // coordinates); the side-based show places it below the gear button
        menu.show(presetMenuButton, javafx.geometry.Side.BOTTOM, 0, 0);
    }

    /**
     * Saves the given name as a new user preset capturing the current settings (Swing
     * {@code saveCurrentAs}, StrategySelectionView.java:663-694): an empty name or a built-in
     * name is rejected (a warning alert for built-in names), an existing preset is overwritten
     * after a confirmation, and the rebuilt combo selects the saved entry.
     *
     * @param input the dialog input, may be {@code null} (cancelled dialog)
     * @return {@code true} if the preset was saved
     */
    private boolean saveCurrentAs(String input) {
        if (proof == null) {
            return false;
        }
        String name = input == null ? "" : input.trim();
        if (name.isEmpty()) {
            return false;
        }
        if (isBuiltInName(name)) {
            if (!verifyRun) {
                new Alert(Alert.AlertType.WARNING, "\"" + name
                    + "\" is the name of a built-in preset. Please choose another name.",
                    ButtonType.OK).showAndWait();
            }
            return false;
        }
        StrategyPresetsSettings settings = getPresetsSettings();
        if (settings.contains(name)) {
            // the headless verify overwrites silently (a showAndWait has nobody to click)
            if (verifyRun) {
                settings.saveOrUpdate(
                    new StrategyPreset(name, currentMaxSteps(), currentStrategyProperties()));
                rebuildPresetCombo(name);
                return true;
            }
            Alert confirm = new Alert(Alert.AlertType.CONFIRMATION,
                "A preset named \"" + name + "\" already exists. Overwrite it?",
                ButtonType.YES, ButtonType.NO);
            if (confirm.showAndWait().orElse(ButtonType.NO) != ButtonType.YES) {
                return false;
            }
        }
        settings.saveOrUpdate(
            new StrategyPreset(name, currentMaxSteps(), currentStrategyProperties()));
        rebuildPresetCombo(name);
        return true;
    }

    /**
     * Saves the current settings to the reserved "Stash" preset (Swing {@code stashCurrent},
     * StrategySelectionView.java:696-702) and selects it in the rebuilt combo.
     */
    private void stashCurrent() {
        if (proof == null) {
            return;
        }
        getPresetsSettings().stash(currentMaxSteps(), currentStrategyProperties());
        rebuildPresetCombo(StrategyPresetsSettings.STASH_NAME);
    }

    /**
     * Renames the selected user-defined preset (Swing {@code renameSelected},
     * StrategySelectionView.java:704-733): an empty/same name aborts, built-in names and
     * existing names are rejected with a warning alert, and the rebuilt combo selects the new
     * name.
     *
     * @param input the dialog input, may be {@code null} (cancelled dialog)
     * @return {@code true} if the preset was renamed
     */
    private boolean renameSelected(String input) {
        PresetEntry selected = presetCombo.getValue();
        if (selected == null || !selected.userDefined()) {
            return false;
        }
        String newName = input == null ? "" : input.trim();
        if (newName.isEmpty() || newName.equals(selected.name())) {
            return false;
        }
        if (isBuiltInName(newName)) {
            if (!verifyRun) {
                new Alert(Alert.AlertType.WARNING, "\"" + newName
                    + "\" is the name of a built-in preset. Please choose another name.",
                    ButtonType.OK).showAndWait();
            }
            return false;
        }
        if (getPresetsSettings().contains(newName)) {
            if (!verifyRun) {
                new Alert(Alert.AlertType.WARNING,
                    "A preset named \"" + newName + "\" already exists.", ButtonType.OK)
                        .showAndWait();
            }
            return false;
        }
        getPresetsSettings().rename(selected.name(), newName);
        rebuildPresetCombo(newName);
        return true;
    }

    /**
     * Deletes the given user-defined preset (Swing {@code deleteUserPreset},
     * StrategySelectionView.java:735-750) and keeps the combo's selection when it was a
     * different entry.
     *
     * @param entry the preset to delete, must be user-defined
     * @return {@code true} if the preset was removed
     */
    private boolean deleteUserPreset(PresetEntry entry) {
        if (entry == null || !entry.userDefined()) {
            return false;
        }
        PresetEntry selected = presetCombo.getValue();
        String keepSelected =
            selected != null && !selected.name().equals(entry.name()) ? selected.name() : null;
        getPresetsSettings().remove(entry.name());
        rebuildPresetCombo(keepSelected);
        return true;
    }

    /**
     * WP-3 (goallist-strategy-info): headless self test of the preset UI ({@code
     * key.fx.verify.goallist}): the entry list (Defaults + built-ins + user presets), the
     * stash/save/rename/delete round trip over {@link StrategyPresetsSettings}, the write-through
     * of the preset application (max steps + one strategy property read back from the proof's
     * settings) and the Apply-button gating ({@code predefChanged}). The previous settings are
     * restored and the created presets removed afterwards.
     *
     * @return a one-line report, {@code "... PASS"} if every assertion holds
     */
    public String verifyPresetCombo() {
        if (!FxUtil.isFxThread()) {
            return FxUtil.callAndWait(this::verifyPresetCombo);
        }
        if (proof == null) {
            return "no proof";
        }
        verifyRun = true;
        StrategySettings settings = proof.getSettings().getStrategySettings();
        int originalSteps = settings.getMaxSteps();
        StrategyProperties originalProperties = settings.getActiveStrategyProperties();
        List<String> originalPresets =
            getPresetsSettings().getPresets().stream().map(StrategyPreset::name).toList();
        boolean pass = true;
        int restored = -1;
        try {
            // entry list: Defaults first, then the built-ins, then the stored user presets
            List<PresetEntry> entries = buildPresetEntries();
            pass &= !entries.isEmpty() && entries.get(0).name().equals("Defaults");
            pass &= entries.size() == 1 + DEFINITION.getFurtherDefaults().size()
                    + originalPresets.size()
                    && entries.get(1).name().equals(
                        DEFINITION.getFurtherDefaults().get(0).name());

            // stash round trip: the reserved "Stash" preset captures the current settings and
            // is selected in the rebuilt combo
            int maxStepsBefore = currentMaxSteps();
            stashCurrent();
            pass &= getPresetsSettings().contains(StrategyPresetsSettings.STASH_NAME);
            pass &= presetCombo.getValue() != null
                    && StrategyPresetsSettings.STASH_NAME.equals(presetCombo.getValue().name());

            // save round trip via the parameterized core method (the menu action delegates to it)
            boolean saved = saveCurrentAs("WP3-verify-preset");
            pass &= saved && getPresetsSettings().contains("WP3-verify-preset")
                    && presetCombo.getValue() != null
                    && "WP3-verify-preset".equals(presetCombo.getValue().name());

            // rename round trip
            pass &= renameSelected("WP3-verify-preset-2");
            pass &= getPresetsSettings().contains("WP3-verify-preset-2")
                    && !getPresetsSettings().contains("WP3-verify-preset")
                    && "WP3-verify-preset-2".equals(presetCombo.getValue().name());
            pass &= !renameSelected("Defaults"); // built-in names are reserved
            pass &= !renameSelected("WP3-verify-preset-2"); // same name aborts

            // write-through: applying a preset writes its max steps (proof settings) and its
            // properties into the proof's live settings and recreates the active strategy
            PresetEntry defaults = buildPresetEntries().get(0);
            adjustingPresetCombo = true;
            try {
                presetCombo.getSelectionModel().select(defaults);
            } finally {
                adjustingPresetCombo = false;
            }
            applySelectedPreset();
            pass &= settings.getMaxSteps() == defaults.maxSteps()
                    && Objects.equals(settings.getActiveStrategyProperties()
                            .getProperty(StrategyProperties.SPLITTING_OPTIONS_KEY),
                        defaults.properties().getProperty(StrategyProperties.SPLITTING_OPTIONS_KEY))
                    && !predefChanged && applyButton.isDisable();

            // the Apply button re-enables after the next widget edit (Swing predefChanged)
            maxStepsSpinner.getValueFactory().setValue(
                maxStepsSpinner.getValue() == VERIFY_MAX_STEPS ? VERIFY_MAX_STEPS + 1
                        : VERIFY_MAX_STEPS);
            pass &= predefChanged && !applyButton.isDisable();

            // delete round trip via the combo's "✕" affordance handler
            PresetEntry userEntry = presetCombo.getItems().stream()
                    .filter(e -> "WP3-verify-preset-2".equals(e.name())).findFirst().orElse(null);
            pass &= userEntry != null && deleteUserPreset(userEntry)
                    && !getPresetsSettings().contains("WP3-verify-preset-2");
        } finally {
            verifyRun = false;
            for (String name : getPresetsSettings().getPresets().stream()
                    .map(StrategyPreset::name).toList()) {
                if (!originalPresets.contains(name)) {
                    getPresetsSettings().remove(name);
                }
            }
            settings.setMaxSteps(originalSteps);
            settings.setActiveStrategyProperties(originalProperties);
            proof.setActiveStrategy(
                getStrategy(proof.getActiveStrategy().name().toString(), originalProperties));
            rebuildPresetCombo(null);
            predefChanged = true;
            restored = settings.getMaxSteps();
            pass &= restored == originalSteps;
        }
        return "entries=" + presetCombo.getItems().size() + " stash/save/rename/delete="
            + (pass ? "ok" : "broken") + " maxSteps=" + originalSteps + "->" + restored + " "
            + (pass ? "PASS" : "FAIL");
    }

    // WP-3: end


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
        // strategy: the merge lock reflects on every refresh (Swing
        // StrategySelectionView.refresh calls reflectParallelProverMergeLock, :863)
        reflectParallelProverMergeLock();
    }

    /**
     * @return the proof whose settings are displayed, or {@code null} if none is attached
     */
    public Proof getProof() {
        return proof;
    }

    /**
     * @return the maximal number of rule applications currently configured for the displayed
     *         proof (Swing {@code currentMaxSteps}, StrategySelectionView.java:603-607)
     */
    private int currentMaxSteps() {
        return proof.getSettings().getStrategySettings().getMaxSteps();
    }

    /**
     * Enables or disables all controls, mirroring {@code StrategySelectionView.enableAll}.
     *
     * @param enable {@code true} to enable the controls
     */
    private void enableAll(boolean enable) {
        content.setDisable(!enable);
        presetCombo.setDisable(!enable);
        presetMenuButton.setDisable(!enable);
        refreshDefaultButton();
    }

    /**
     * WP-3: updates the Apply button enablement (Swing {@code refreshDefaultButton},
     * StrategySelectionView.java:897-907): enabled while a proof is selected and a chosen preset
     * has been changed by a widget edit ({@code predefChanged}); without a proof the preset
     * controls are disabled as well.
     */
    private void refreshDefaultButton() {
        if (proof != null) {
            applyButton.setDisable(!predefChanged);
        } else {
            applyButton.setDisable(true);
        }
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
        // WP-3: a widget edit re-enables the preset Apply button (Swing
        // MaxRuleAppSlider change listener, StrategySelectionView.java:262-265)
        predefChanged = true;
        refreshDefaultButton();
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
        // WP-3: a widget edit re-enables the preset Apply button (Swing newButton action
        // listener, StrategySelectionView.java:406-411)
        predefChanged = true;
        refreshDefaultButton();
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
        updateStrategySettings(proof.getActiveStrategy().name().toString(),
            currentStrategyProperties());
    }

    /**
     * Writes the given strategy properties through to the live strategy settings: they are
     * stored in the global default settings as well as in the proof's settings, and the active
     * strategy is recreated from the matching {@link StrategyFactory} (mirroring {@code
     * StrategySelectionView.updateStrategySettings(String, StrategyProperties)},
     * StrategySelectionView.java:976-989 — the Swing original additionally refreshes the
     * widgets, which {@link #applySelectedPreset} does after the preset application).
     */
    private void updateStrategySettings(String strategyName, StrategyProperties properties) {
        Strategy<Goal> strategy = getStrategy(strategyName, properties);
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
