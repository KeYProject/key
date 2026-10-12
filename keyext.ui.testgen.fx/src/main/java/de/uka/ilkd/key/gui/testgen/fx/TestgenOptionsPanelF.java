/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.testgen.fx;

import java.io.File;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Node;
import javafx.scene.control.Button;
import javafx.scene.control.CheckBox;
import javafx.scene.control.Control;
import javafx.scene.control.Label;
import javafx.scene.control.Spinner;
import javafx.scene.control.SpinnerValueFactory;
import javafx.scene.control.TextField;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.GridPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.Region;
import javafx.stage.DirectoryChooser;

import org.jspecify.annotations.NullMarked;

/**
 * The test-generation options panel, FX port of {@code TestgenOptionsPanel} (Swing
 * TestgenOptionsPanel.java:14-157): the symbolic-execution/macro options, the maximal unwinds
 * and concurrent SMT-process numbers, the output folder, and the duplicate/RFL/invariant/
 * post-condition toggles over the global singleton {@link TestGenerationSettingsF}.
 * <p>
 * The panel is used at two surfaces (the Swing {@code TestgenOptionsPanel} is likewise both the
 * Settings-dialog entry and the eastern edge of {@code TGInfoDialog}, TGInfoDialog.java:126):
 * <ul>
 * <li>in the Settings dialog through {@link TestgenSettingsProviderF} (the {@code live=false}
 * mode: the edits stay in the widgets and are written back on Apply/OK like the Swing
 * {@code applySettings}, TestgenOptionsPanel.java:153-157), and</li>
 * <li>embedded in the {@code TestGenResultsDialogF} run dialog ({@code live=true}: every edit
 * writes into the global settings immediately, so options can be changed right before a run —
 * the Swing embedded panel edits a working copy that is never applied from the run dialog, so
 * its edits were lost; writing live is the deliberate FX change).</li>
 * </ul>
 * <b>KNOWN-SIMPLIFIED:</b> the dead OpenJML/Objenesis file choosers of the Swing original are
 * dropped (their setters are commented out, TestgenOptionsPanel.java:97-107). All widgets are
 * created lazily in the constructor call: every {@code javafx.scene.control.Control} triggers
 * the FX toolkit in its class initializer, so this class must not be instantiated headless.
 */
@NullMarked
final class TestgenOptionsPanelF {

    private static final String INFO_APPLY_SYMBOLIC_EX =
        "Performs bounded symbolic execution on the current proof tree."
            + " More precisely, the TestGen Macro is executed which the user can also manually execute by right-clicking "
            + "on the proof tree and selecting Strategy Macros->TestGen.";
    private static final String INFO_SAVE_TO =
        "Choose the folder where the test case files will be written.";
    private static final String INFO_MAX_PROCESSES =
        "Maximal number of SMT processes that are allowed to " + "run concurrently.";
    private static final String INFO_INVARIANT_FOR_ALL =
        "Includes class invariants in the test data constraints. "
            + "I.e., require the class invariant of all created objects to be true in the initial state.";
    private static final String INFO_MAX_UNWINDS =
        "Maximal number of loop unwinds or method calls on a branch that "
            + "is symbolically executed when using the Strategy Macro \"TestGen\". The Strategy Macro is available"
            + " by right-click on the proof tree.";
    private static final String INFO_REMOVE_DUPLICATES =
        "Generate a single testcase for two or more nodes which "
            + "represent the same test data constraint. Two different nodes may represent the same test data constraint, "
            + "because some formulas from the nodes which cannot be translated into a test case may be filtered out "
            + "from the test data constraint.";
    private static final String INFO_RFL_SELECTION =
        "Enables initialization of protected, private, and ghost fields " + "with test data, "
            + "as well as creation of objects from classes which have no default constructor "
            + "(requires the Objenesis library)."
            + "This functionality is enabled by RFL.java which is generated along the test suite. Please note, "
            + "a runtime checker may not be able to handle the generated code.";
    private static final String INFO_INCLUDE_POSTCONDITION =
        "Includes the negated post condition in the test data "
            + "constraint when generating test data. The post condition can only be included for paths (branches)"
            + " where symbolic execution has finished.";

    private final CheckBox symbolicEx;
    private final Spinner<Integer> maxUnwinds;
    private final CheckBox invariantForAll;
    private final CheckBox includePostCondition;
    private final Spinner<Integer> maxProcesses;
    private final TextField saveToFilePanel;
    private final CheckBox removeDuplicates;
    private final CheckBox checkboxRFL;

    private final Node panel;

    /**
     * Creates the panel.
     *
     * @param live whether every edit writes into the global {@link TestGenerationSettingsF}
     *        immediately (the embedded run-dialog mode; the Settings-dialog mode keeps the
     *        edits in the widgets until {@link #applySettings()})
     */
    TestgenOptionsPanelF(boolean live) {
        symbolicEx = new CheckBox("Apply symbolic execution");
        maxUnwinds = intSpinner(0, Integer.MAX_VALUE, 1, 3);
        invariantForAll = new CheckBox("Require invariant for all objects");
        includePostCondition = new CheckBox("Include post condition");
        maxProcesses = intSpinner(0, Integer.MAX_VALUE, 1, 1);
        saveToFilePanel = new TextField();
        removeDuplicates = new CheckBox("Remove duplicates");
        checkboxRFL = new CheckBox("Use reflection framework");
        setTooltips();
        symbolicEx.setSelected(false);
        invariantForAll.setSelected(true);
        includePostCondition.setSelected(false);
        removeDuplicates.setSelected(true);
        checkboxRFL.setSelected(false);
        if (live) {
            TestGenerationSettingsF global = new TestGenerationSettingsF();
            symbolicEx.selectedProperty()
                    .addListener((obs, o, v) -> global.setApplySymbolicEx(v));
            maxUnwinds.valueProperty()
                    .addListener((obs, o, v) -> global.setMaxUnwinds(Math.max(0, v)));
            invariantForAll.selectedProperty()
                    .addListener((obs, o, v) -> global.setInvariantForAll(v));
            includePostCondition.selectedProperty()
                    .addListener((obs, o, v) -> global.setIncludePostCondition(v));
            maxProcesses.valueProperty()
                    .addListener((obs, o, v) -> global.setConcurrentProcesses(Math.max(0, v)));
            saveToFilePanel.textProperty().addListener((obs, o, v) -> global.setOutputPath(v));
            removeDuplicates.selectedProperty()
                    .addListener((obs, o, v) -> global.setRemoveDuplicates(v));
            checkboxRFL.selectedProperty().addListener((obs, o, v) -> global.setUseRFL(v));
        }
        panel = buildPanel();
    }

    /** @return the panel node (a {@link GridPane} of label/input rows) */
    Node getNode() {
        return panel;
    }

    /** Re-reads the global settings into the widgets (Swing getPanel, :139-151). */
    void readFromSettings() {
        TestGenerationSettingsF settings = new TestGenerationSettingsF();
        symbolicEx.setSelected(settings.applySymbolicEx());
        maxUnwinds.getValueFactory().setValue(settings.maxUnwinds());
        invariantForAll.setSelected(settings.invariantForAll());
        includePostCondition.setSelected(settings.includePostCondition());
        maxProcesses.getValueFactory().setValue(settings.processes());
        saveToFilePanel.setText(settings.outputFolderPath());
        removeDuplicates.setSelected(settings.removeDuplicates());
        checkboxRFL.setSelected(settings.useRFL());
    }

    /** Writes the widget states back into the global settings singleton (Swing applySettings). */
    void applySettings() {
        TestGenerationSettingsF global = new TestGenerationSettingsF();
        global.setApplySymbolicEx(symbolicEx.isSelected());
        global.setInvariantForAll(invariantForAll.isSelected());
        global.setIncludePostCondition(includePostCondition.isSelected());
        global.setMaxUnwinds(Math.max(0, maxUnwinds.getValue()));
        global.setConcurrentProcesses(Math.max(0, maxProcesses.getValue()));
        global.setOutputPath(saveToFilePanel.getText());
        global.setRemoveDuplicates(removeDuplicates.isSelected());
        global.setUseRFL(checkboxRFL.isSelected());
    }

    /**
     * The options panel: a {@link GridPane} of label/input rows with tooltips (the Swing
     * {@code TestgenOptionsPanel} uses a {@code GridBagLayout} with the same rows,
     * TestgenOptionsPanel.java:67-108).
     */
    private Node buildPanel() {
        GridPane grid = new GridPane();
        grid.setHgap(8);
        grid.setVgap(8);
        grid.setPadding(new Insets(12));
        int row = 0;
        addRow(grid, row++, null, symbolicEx);
        addRow(grid, row++, "Maximal unwinds:", maxUnwinds);
        addRow(grid, row++, null, invariantForAll);
        addRow(grid, row++, null, includePostCondition);
        addRow(grid, row++, "Concurrent processes:", maxProcesses);
        addRow(grid, row++, "Store test cases to folder:", saveToRow());
        addRow(grid, row++, null, removeDuplicates);
        addRow(grid, row, null, checkboxRFL);
        return grid;
    }

    /** One label + input row of the panel (or the input alone when {@code title == null}). */
    private void addRow(GridPane grid, int row, String title, Node input) {
        if (title != null) {
            Label label = new Label(title);
            label.setAlignment(Pos.CENTER_LEFT);
            if (input instanceof Control control) {
                label.setTooltip(control.getTooltip());
            }
            grid.add(label, 0, row);
            grid.add(input, 1, row);
        } else {
            grid.add(input, 0, row);
        }
        if (input instanceof Region region) {
            region.setMaxWidth(Double.MAX_VALUE);
        }
        GridPane.setHgrow(input, Priority.ALWAYS);
    }

    /** The output-folder row: the text field plus a directory-chooser button. */
    private HBox saveToRow() {
        Button browse = new Button("...");
        browse.setTooltip(new Tooltip(INFO_SAVE_TO));
        browse.setOnAction(e -> {
            DirectoryChooser chooser = new DirectoryChooser();
            chooser.setTitle("Choose the test-case output folder");
            File initial = new File(saveToFilePanel.getText());
            if (initial.isDirectory()) {
                chooser.setInitialDirectory(initial);
            }
            File selected = saveToFilePanel.getScene() == null
                    ? null
                    : chooser.showDialog(saveToFilePanel.getScene().getWindow());
            if (selected != null && selected.isDirectory()) {
                saveToFilePanel.setText(selected.getAbsolutePath());
            }
        });
        HBox.setHgrow(saveToFilePanel, Priority.ALWAYS);
        return new HBox(4, saveToFilePanel, browse);
    }

    private void setTooltips() {
        symbolicEx.setTooltip(new Tooltip(INFO_APPLY_SYMBOLIC_EX));
        maxUnwinds.setTooltip(new Tooltip(INFO_MAX_UNWINDS));
        invariantForAll.setTooltip(new Tooltip(INFO_INVARIANT_FOR_ALL));
        includePostCondition.setTooltip(new Tooltip(INFO_INCLUDE_POSTCONDITION));
        maxProcesses.setTooltip(new Tooltip(INFO_MAX_PROCESSES));
        saveToFilePanel.setTooltip(new Tooltip(INFO_SAVE_TO));
        removeDuplicates.setTooltip(new Tooltip(INFO_REMOVE_DUPLICATES));
        checkboxRFL.setTooltip(new Tooltip(INFO_RFL_SELECTION));
    }

    private static Spinner<Integer> intSpinner(int min, int max, int step, int value) {
        Spinner<Integer> spinner =
            new Spinner<>(new SpinnerValueFactory.IntegerSpinnerValueFactory(min, max, value,
                step));
        spinner.setEditable(true);
        return spinner;
    }
}
