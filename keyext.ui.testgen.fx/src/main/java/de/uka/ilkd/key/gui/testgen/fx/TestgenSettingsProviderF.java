/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.testgen.fx;

import java.io.File;
import java.lang.reflect.InvocationHandler;
import java.lang.reflect.Proxy;
import java.util.List;
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

import de.uka.ilkd.key.gui.fx.settings.SettingsProviderF;

import org.jspecify.annotations.NullMarked;

/**
 * The test-generation options panel, FX port of {@code TestgenOptionsPanel} (Swing
 * TestgenOptionsPanel.java:14-157): the symbolic-execution/macro options, the maximal unwinds
 * and concurrent SMT-process numbers, the output folder, and the duplicate/RFL/invariant/
 * post-condition toggles — reading and writing the global singleton
 * {@link TestGenerationSettingsF} (TestgenOptionsPanel.getPanel/getDescription/applySettings,
 * TestgenOptionsPanel.java:134-157).
 * <p>
 * <b>KNOWN-SIMPLIFIED (proxy provider):</b> {@code SettingsProviderF.getPanel/apply} are declared
 * with a {@code MainWindowF} parameter, and any {@code MainWindowF} type use in this module
 * forces javac to complete the class file, which fails ("Cannot attach type annotations ... to
 * MainWindowF.lastEnvironment: class file for de.uka.ilkd.key.control.KeYEnvironment not
 * found"). The provider is therefore a {@link java.lang.reflect.Proxy} implementing
 * {@code SettingsProviderF} without naming the window type at compile time; the window arrives as
 * a plain {@code Object} argument of the reflective dispatch and is forwarded to
 * {@link TestgenExtensionF#captureWindow(Object)} (the extension's only compile-safe window
 * channel).
 * <p>
 * <b>KNOWN-SIMPLIFIED (panel):</b> the Swing panel subclasses the Swing {@code SettingsPanel}
 * base (row/validator/chooser helpers) and installs change listeners that write into a working
 * copy of the settings as the user edits; the FX port builds a plain {@link GridPane} of
 * label/input rows (the settings host wraps the panel in a {@code ScrollPane}), reads the widgets
 * in {@code apply} only (leaving the dialog through OK/Apply is the only path that persists, so
 * the result is identical), and drops the dead OpenJML/Objenesis file choosers of the Swing
 * original (their setters are commented out, TestgenOptionsPanel.java:97-107).
 */
@NullMarked
final class TestgenSettingsProviderF {

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
            + "because some formulas from the nodes which cannot be translated into a test case may be filtered out from "
            + "the test data constraint.";
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

    private TestgenSettingsProviderF() {
    }

    /**
     * Creates the {@link SettingsProviderF} entry (a reflective {@link Proxy}) for the given
     * extension, forwarding the main window of every panel access to
     * {@link TestgenExtensionF#captureWindow(Object)}.
     *
     * @param extension the owning extension, notified of the main window
     * @return the settings provider, never {@code null}
     */
    static SettingsProviderF create(TestgenExtensionF extension) {
        return (SettingsProviderF) Proxy.newProxyInstance(SettingsProviderF.class
                .getClassLoader(),
            new Class<?>[] { SettingsProviderF.class },
            new SettingsState(extension));
    }

    /**
     * The {@link InvocationHandler} of the settings provider + the panel widgets: dispatching the
     * {@code SettingsProviderF} methods (routed by name, mirroring the Swing original's
     * semantics) and building the options panel node.
     * <p>
     * The widget fields are deliberately built lazily in {@link #ensureWidgets()}: every
     * {@code javafx.scene.control.Control} triggers the FX toolkit in its class initializer
     * ("Toolkit not initialized"), so neither the provider proxy nor the extension must touch
     * Controls until the settings panel is really opened inside the running app.
     */
    private static final class SettingsState implements InvocationHandler {

        private final TestgenExtensionF extension;

        private CheckBox symbolicEx;
        private Spinner<Integer> maxUnwinds;
        private CheckBox invariantForAll;
        private CheckBox includePostCondition;
        private Spinner<Integer> maxProcesses;
        private TextField saveToFilePanel;
        private CheckBox removeDuplicates;
        private CheckBox checkboxRFL;

        private Node panel;

        SettingsState(TestgenExtensionF extension) {
            this.extension = extension;
        }

        /** The SettingsProviderF dispatch of the reflective provider. */
        @Override
        public Object invoke(Object proxy, java.lang.reflect.Method method, Object[] args) {
            switch (method.getName()) {
                case "getDescription" -> {
                    // extension: MP9.5 — Swing TestgenOptionsPanel.getDescription
                    // (TestgenOptionsPanel.java:134)
                    return "TestGen";
                }
                case "getPanel" -> {
                    // extension: MP9.5 — Swing TestgenOptionsPanel.getPanel
                    // (TestgenOptionsPanel.java:139-151): re-read the global settings.
                    if (args != null && args.length > 0 && args[0] != null) {
                        extension.captureWindow(args[0]);
                    }
                    return panel();
                }
                case "apply" -> {
                    // extension: MP9.5 — Swing TestgenOptionsPanel.applySettings
                    // (TestgenOptionsPanel.java:153): write the widget states back.
                    if (args != null && args.length > 0 && args[0] != null) {
                        extension.captureWindow(args[0]);
                    }
                    applySettings();
                    return null;
                }
                case "getChildProviders" -> {
                    return List.of();
                }
                case "getPriorityOfSettings" -> {
                    return 0;
                }
                case "contains" -> {
                    // the SettingsProviderF default: description substring match.
                    String substring =
                        args == null || args.length == 0 || args[0] == null ? null
                                : args[0].toString();
                    return substring != null && !substring.isEmpty()
                            && "TestGen".toLowerCase().contains(substring.toLowerCase());
                }
                case "equals" -> {
                    return args != null && args.length == 1 && args[0] == proxy;
                }
                case "hashCode" -> {
                    return System.identityHashCode(proxy);
                }
                case "toString" -> {
                    return "TestGenerationSettingsProvider(proxy)";
                }
                default -> {
                }
            }
            return null;
        }

        /** Builds (once) and returns the options panel, re-reading the global settings. */
        private Node panel() {
            if (panel == null) {
                ensureWidgets();
                panel = buildPanel();
            }
            TestGenerationSettingsF settings = new TestGenerationSettingsF();
            symbolicEx.setSelected(settings.applySymbolicEx());
            maxUnwinds.getValueFactory().setValue(settings.maxUnwinds());
            invariantForAll.setSelected(settings.invariantForAll());
            includePostCondition.setSelected(settings.includePostCondition());
            maxProcesses.getValueFactory().setValue(settings.processes());
            saveToFilePanel.setText(settings.outputFolderPath());
            removeDuplicates.setSelected(settings.removeDuplicates());
            checkboxRFL.setSelected(settings.useRFL());
            return panel;
        }

        /** Writes the widget states back into the global settings singleton. */
        private void applySettings() {
            if (symbolicEx == null) {
                // the panel was never opened, nothing was edited to persist.
                return;
            }
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

        /** Creates the widget controls (lazily: Control class-init requires the FX toolkit). */
        private void ensureWidgets() {
            if (symbolicEx != null) {
                return;
            }
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
}
