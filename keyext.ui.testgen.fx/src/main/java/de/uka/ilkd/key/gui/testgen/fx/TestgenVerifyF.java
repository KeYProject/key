/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2,
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.testgen.fx;

import java.lang.reflect.Method;
import java.lang.reflect.Proxy;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.control.Button;
import javafx.scene.control.CheckBox;
import javafx.scene.control.DialogPane;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.Spinner;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.control.TextArea;
import javafx.scene.control.TreeItem;
import javafx.scene.layout.BorderPane;
import javafx.stage.Stage;
import javafx.stage.Window;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.extension.KeYGuiExtensionFacadeF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.gui.fx.keyshortcuts.KeyStrokeManagerF;
import de.uka.ilkd.key.gui.fx.smt.CETreeF;
import de.uka.ilkd.key.gui.fx.smt.InformationWindowF;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.DefaultSMTSettings;
import de.uka.ilkd.key.settings.NewSMTTranslationSettings;
import de.uka.ilkd.key.settings.ProofDependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.communication.AbstractSolverSocket;
import de.uka.ilkd.key.smt.model.Heap;
import de.uka.ilkd.key.smt.model.Location;
import de.uka.ilkd.key.smt.model.LocationSet;
import de.uka.ilkd.key.smt.model.Model;
import de.uka.ilkd.key.smt.model.ObjectVal;
import de.uka.ilkd.key.smt.model.Sequence;
import de.uka.ilkd.key.smt.ProblemTypeInformation;
import de.uka.ilkd.key.smt.ModelExtractor;
import de.uka.ilkd.key.smt.SMTObjTranslator;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;
import de.uka.ilkd.key.smt.lang.SMTSort;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Headless verify harness for the TestGen extension parity work ({@code key.fx.verify.testgen},
 * forwarded by key.ui.fx/build.gradle and invoked reflectively by {@code MainWindowF}): a self
 * test of the WP-7 testgen pieces, all stub-based (no real test-case generation or counterexample
 * run — the real SMT end to end run is the {@code key.fx.verify.smt} hook):
 * <ol>
 * <li>the extension capability surface (C1/C2): {@code ToolbarF}/{@code StartupF} implemented, the
 * two toolbar buttons ("Generate Testcases...", "Search for Counterexample") build and the
 * generate button is enabled for the loaded proof, the "Test Case Generation" menu carries the
 * two items with the {@code KeyStrokeManagerF} accelerator of the {@code TestGenMacro},</li>
 * <li>the options panel (C5): the Settings-dialog mode ({@code live=false}) renders and round
 * trips through {@code readFromSettings/applySettings}, the live mode ({@code live=true}) writes
 * an edited spinner value into the global {@link TestGenerationSettingsF} immediately,</li>
 * <li>the run dialogs (C3/C4): both {@code TestGenResultsDialogF} (with the embedded live options
 * panel on its right edge) and {@code CounterExampleResultsDialogF} render in their idle mode
 * (Start enabled, Stop disabled, empty log),</li>
 * <li>the counterexample model tree (C6): a stub SMT {@link Model} renders in {@link CETreeF}
 * with the Constants/Heaps/Location Sets/Sequences rows, and the {@link InformationWindowF}
 * retitles to "Counterexample ..." for the stub Z3 CE solver and adds the Counterexample and Help
 * tabs next to the information tabs,</li>
 * <li>the cooperative stop (C3/C4): {@code TestGenerationTaskF.requestStop()} sets the stop flag
 * and {@code TestgenReflectionF.stopLauncher} stops a (never-launched) {@code SolverLauncher}
 * without an exception.</li>
 * </ol>
 * <p>
 * {@code MainWindowF} is deliberately not named in this module (the class-file completion quirk
 * of {@link TestgenSettingsProviderF}); the main window instance for the reflective toolbar/menu
 * dispatch is obtained via reflection. The harness must be called on the JavaFX thread after a
 * demo proof has been loaded.
 */
@NullMarked
public final class TestgenVerifyF {

    private static final Logger LOGGER = LoggerFactory.getLogger(TestgenVerifyF.class);

    private TestgenVerifyF() {
    }

    /**
     * Runs the TestGen extension self test.
     *
     * @param owner the owner window for the dialogs
     * @param proof the loaded demo proof
     * @param mediator the application mediator
     * @return the one-line report ending in {@code PASS} or {@code FAIL}
     */
    public static String run(Window owner, @Nullable Proof proof, KeYMediatorF mediator) {
        if (proof == null) {
            return "TestGen verify: SKIP (no proof loaded)";
        }
        Stage stage = owner instanceof Stage s ? s : null;
        TestGenResultsDialogF generateDialog = null;
        CounterExampleResultsDialogF ceDialog = null;
        int oldMaxUnwinds = new TestGenerationSettingsF().maxUnwinds();
        try {
            TestgenExtensionF extension = findExtension();
            check(extension != null, "testgen extension registered via the service loader");
            if (extension == null) {
                return "TestGen verify: FAIL (extension not registered)";
            }

            // (1) extension capability surface (C1/C2) — the typed capability asserts like the
            // unit test, the control trees through the reflective window dispatch (MainWindowF
            // is not nameable in this module)
            check(extension instanceof KeYGuiExtensionF.ToolbarF, "ToolbarF implemented (WP-7)");
            check(extension instanceof KeYGuiExtensionF.StartupF, "StartupF implemented (WP-7)");
            check(extension instanceof KeYGuiExtensionF.MainMenuF, "MainMenuF implemented");
            check(extension instanceof KeYGuiExtensionF.SettingsF, "SettingsF implemented");
            Class<?> mainWindowClass = Class.forName("de.uka.ilkd.key.gui.fx.MainWindowF");
            Object mainWindow = mainWindowClass.getMethod("getInstance").invoke(null);
            Method toolbarMethod =
                extension.getClass().getMethod("getToolbarControls", mainWindowClass,
                    KeYMediatorF.class);
            List<?> toolbar = (List<?>) toolbarMethod.invoke(extension, mainWindow, mediator);
            check(toolbar.size() == 2, "the toolbar carries the two action buttons");
            Button generateButton = (Button) toolbar.get(0);
            Button counterExampleButton = (Button) toolbar.get(1);
            check("Generate Testcases...".equals(generateButton.getText()),
                "generate button carries the Swing TestGenerationAction name");
            check("Search for Counterexample".equals(counterExampleButton.getText()),
                "counterexample button carries the Swing CounterExampleAction name");
            check(!TestgenReflectionF.z3CeInstalled() || isAutoMode(mediator)
                    || !generateButton.isDisabled(),
                "generate button enabled for the loaded proof when z3 is installed "
                    + "and no run is active");
            Method menusMethod =
                extension.getClass().getMethod("getMenus", mainWindowClass, KeYMediatorF.class);
            List<?> menus = (List<?>) menusMethod.invoke(extension, mainWindow, mediator);
            check(menus.size() == 1 && menus.get(0) instanceof Menu menu
                    && "Test Case Generation".equals(menu.getText())
                    && menu.getItems().size() == 2,
                "the 'Test Case Generation' main menu carries the two Swing actions");
            if (menus.size() == 1 && menus.get(0) instanceof Menu menu) {
                MenuItem generateItem = menu.getItems().get(0);
                check(
                    generateItem.getAccelerator() != null && generateItem.getAccelerator()
                            .equals(KeyStrokeManagerF.getInstance()
                                    .binding(TESTGEN_MACRO_ACTION_ID).orElse(null)),
                    "the macro default shortcut (WP-7 C2) drives the generate item accelerator");
            }

            // (2) options panel (C5): the Settings-dialog mode and the live embedded mode
            TestgenOptionsPanelF settingsMode = new TestgenOptionsPanelF(false);
            check(settingsMode.getNode() != null, "the settings-mode options panel renders");
            settingsMode.readFromSettings();
            settingsMode.applySettings();
            TestgenOptionsPanelF liveMode = new TestgenOptionsPanelF(true);
            List<Spinner> spinners = new ArrayList<>();
            collect(Spinner.class, liveMode.getNode(), spinners);
            check(spinners.size() == 2, "the live options panel has the two number spinners");
            // the maximal-unwinds spinner starts at 3 (the concurrent-process spinner at 1);
            // editing it must write into the global settings immediately (the FX change)
            Spinner<?> unwinds = spinners.stream()
                    .filter(sp -> ((Number) sp.getValue()).intValue() == 3).findFirst().orElse(null);
            check(unwinds != null, "the maximal-unwinds spinner is present");
            if (unwinds != null) {
                @SuppressWarnings("unchecked")
                Spinner<Integer> unwindsSpinner = (Spinner<Integer>) unwinds;
                unwindsSpinner.getValueFactory().setValue(oldMaxUnwinds + 5);
                check(new TestGenerationSettingsF().maxUnwinds() == oldMaxUnwinds + 5,
                    "the live options panel writes the edit into the global settings");
            }

            // (3) run dialogs (C3/C4): idle render modes; the generate dialog embeds the live
            // options panel on its right edge (C5)
            generateDialog = new TestGenResultsDialogF(null, stage);
            generateDialog.show();
            check(generateDialog.isShowing(), "the generation run dialog renders");
            checkRunDialogIdle(generateDialog.getDialogPane(), "generation run dialog");
            BorderPane generateRoot = (BorderPane) generateDialog.getDialogPane().getContent();
            List<CheckBox> embeddedOptions = new ArrayList<>();
            collect(CheckBox.class, generateRoot.getRight(), embeddedOptions);
            check(embeddedOptions.size() == 8,
                "the embedded live options panel (8 toggles) sits on the right edge (C5)");
            generateDialog.close();
            check(!generateDialog.isShowing(), "the generation run dialog closes");

            ceDialog = new CounterExampleResultsDialogF(null, stage);
            ceDialog.show();
            check(ceDialog.isShowing(), "the counterexample run dialog renders");
            checkRunDialogIdle(ceDialog.getDialogPane(), "counterexample run dialog");
            ceDialog.close();

            // (4) counterexample model tree (C6): a stub SMT model renders in CETreeF
            CETreeF ceTree = new CETreeF(stubModel());
            check(ceTree.getTreeComponent().getRoot() != null
                    && "Model".equals(ceTree.getTreeComponent().getRoot().getValue()),
                "the model tree root is 'Model'");
            check(rootChildLabels(ceTree).equals(List.of("Constants", "Heaps", "Location Sets",
                "Sequences")), "the model tree has the four model categories");
            TreeItem<String> heaps = rootChild(ceTree, 1);
            check(heaps != null && heaps.getChildren().size() == 1
                    && "#o1".equals(heaps.getChildren().get(0).getValue()),
                "the heap lists the stub object #o1");
            if (heaps != null && !heaps.getChildren().isEmpty()) {
                List<String> objectRows = labels(heaps.getChildren().get(0));
                check(objectRows.contains("Type=java.lang.Object")
                        && objectRows.contains("Length=0") && objectRows.contains("Fields"),
                    "the object row carries the general properties and the fields node");
                TreeItem<String> fields = child(heaps.getChildren().get(0), "Fields");
                check(fields != null && labels(fields).contains("x=#o0"),
                    "the fields node lists the stub field x=#o0");
            }
            TreeItem<String> locsets = rootChild(ceTree, 2);
            check(locsets != null && locsets.getChildren().size() == 1
                    && "#l1".equals(locsets.getChildren().get(0).getValue())
                    && labels(locsets.getChildren().get(0)).contains("(#o1, x)"),
                "the location-set row lists the stub location");
            TreeItem<String> sequences = rootChild(ceTree, 3);
            check(sequences != null && sequences.getChildren().size() == 1
                    && "#s1".equals(sequences.getChildren().get(0).getValue())
                    && labels(sequences.getChildren().get(0)).contains("Length=2")
                    && labels(sequences.getChildren().get(0)).contains("[0]=true"),
                "the sequence row lists the length and the values");

            // and the information window (C6): for the stub Z3 CE solver with a query model the
            // window is retitled "Counterexample ..." and gains the model + help tabs
            InformationWindowF noSolver =
                new InformationWindowF(owner, null, "Information window",
                    List.of(new InformationWindowF.Information("Solver Input", "text", "z3")));
            check("Information window".equals(noSolver.getTitle()),
                "without a solver the window title is unchanged");
            check(!tabTitles(noSolver).contains("Counterexample"),
                "without a solver no counterexample tabs are added");
            noSolver.close();

            InformationWindowF ceWindow =
                new InformationWindowF(owner, stubSolver(stubModelExtractor()), "Information "
                    + "window",
                    List.of(new InformationWindowF.Information("Solver Input", "text", "z3")));
            check(ceWindow.getTitle().startsWith("Counterexample"),
                "the Z3 CE window is retitled 'Counterexample ...' (WP-7 C6)");
            List<String> titles = tabTitles(ceWindow);
            check(titles.contains("Counterexample") && titles.contains("Help")
                    && titles.contains("Solver Input"),
                "the counterexample, help and information tabs are present: " + titles);
            ceWindow.close();

            // (5) cooperative stop (C3/C4): the stop flag of the generation task and the
            // launcher stop (the Swing stopSMTLauncher/interruptionPerformed parity)
            Object ui = TestgenReflectionF.uiOf(mainWindow);
            TestGenerationTaskF task =
                new TestGenerationTaskF(mediator, ui, proof, new RecordingSink());
            task.requestStop();
            check(task.isStopRequested(), "requestStop sets the cooperative stop flag");
            SolverLauncher launcher = new SolverLauncher(new DefaultSMTSettings(
                ProofDependentSMTSettings.getDefaultSettingsData(),
                ProofIndependentSMTSettings.getDefaultSettingsData(),
                new NewSMTTranslationSettings(), proof));
            TestgenReflectionF.stopLauncher(launcher);
            LOGGER.info("TestGen verify: capability surface, options panel, run dialogs, CE "
                + "model tree and cooperative stop OK (no real generation run)");
            return "TestGen verify: extension wiring + options panel + run dialogs + CE model "
                + "tree + cooperative stop without a real generation run PASS";
        } catch (RuntimeException | AssertionError | ReflectiveOperationException e) {
            LOGGER.error("TestGen verify failed", e);
            return "TestGen verify: FAIL (" + e + ")";
        } finally {
            if (generateDialog != null) {
                generateDialog.close();
            }
            if (ceDialog != null) {
                ceDialog.close();
            }
            new TestGenerationSettingsF().setMaxUnwinds(oldMaxUnwinds);
        }
    }

    /** action id of the TestGenMacro (the {@code KeyStrokeManagerF} default, WP-7 C2). */
    private static final String TESTGEN_MACRO_ACTION_ID =
        "de.uka.ilkd.key.testgen.macros.TestGenMacro";

    /** whether the mediator reports a running auto mode (the buttons are then disabled). */
    private static boolean isAutoMode(KeYMediatorF mediator) {
        return TestgenReflectionF.autoModePropertyOf(mediator)
                instanceof javafx.beans.property.ReadOnlyBooleanProperty p && p.get();
    }

    private static TestgenExtensionF findExtension() {
        return KeYGuiExtensionFacadeF.getExtensions().stream()
                .filter(TestgenExtensionF.class::isInstance)
                .map(TestgenExtensionF.class::cast).findFirst().orElse(null);
    }

    /** The idle-button/log assertions shared by the two run dialogs (C3/C4). */
    private static void checkRunDialogIdle(DialogPane pane, String what) {
        List<Button> buttons = new ArrayList<>();
        collect(Button.class, pane, buttons);
        Button start = buttonByText(buttons, "Start");
        Button stop = buttonByText(buttons, "Stop");
        Button close = buttonByText(buttons, "Close");
        check(start != null && !start.isDisable(), what + ": Start enabled while idle");
        check(stop != null && stop.isDisable(), what + ": Stop disabled while idle");
        check(close != null && !close.isDisable(), what + ": Close enabled while idle");
        List<TextArea> logs = new ArrayList<>();
        collect(TextArea.class, pane, logs);
        check(logs.size() == 1 && logs.get(0).getText().isEmpty(),
            what + ": empty pipeline log");
    }

    private static Button buttonByText(List<Button> buttons, String text) {
        return buttons.stream().filter(b -> text.equals(b.getText())).findFirst().orElse(null);
    }

    // ------------------------------------------------------------------ stub model

    /**
     * A stub SMT model (fake/stub data like the Swing dialog tests): one constant {@code c1}
     * pointing to the heap object {@code #o1} with the field {@code x=#o0}, one location set
     * {@code #l1} with the location {@code (#o1, x)} and one sequence {@code #s1}.
     */
    private static Model stubModel() {
        Model model = new Model();
        ProblemTypeInformation types = new ProblemTypeInformation(null);
        types.putConstantType("c1", new SMTSort(SMTObjTranslator.OBJECT_SORT));
        model.setTypes(types);
        model.addConstant("c1", "#o1");
        Heap heap = new Heap("heap");
        ObjectVal object = new ObjectVal("#o1");
        object.setFieldvalues(Map.of("x", "#o0"));
        heap.add(object);
        model.addHeap(heap);
        LocationSet locset = new LocationSet("#l1");
        locset.add(new Location("#o1", "x"));
        model.addLocationSet(locset);
        Sequence sequence = new Sequence(2, "#s1");
        sequence.set(0, "true");
        sequence.set(1, "false");
        model.addSequence(sequence);
        return model;
    }

    /**
     * A stub {@code ModelExtractor} whose model is the stub model (the {@code InformationWindowF}
     * reads {@code solver.getSocket().getQuery().getModel()}).
     */
    private static ModelExtractor stubModelExtractor() {
        ModelExtractor extractor = new ModelExtractor();
        Model model = extractor.getModel();
        ProblemTypeInformation types = new ProblemTypeInformation(null);
        types.putConstantType("c1", new SMTSort(SMTObjTranslator.OBJECT_SORT));
        model.setTypes(types);
        model.addConstant("c1", "#o1");
        Heap heap = new Heap("heap");
        ObjectVal object = new ObjectVal("#o1");
        object.setFieldvalues(Map.of("x", "#o0"));
        heap.add(object);
        model.addHeap(heap);
        return extractor;
    }

    /**
     * A stub Z3 CE solver (fake/stub data): its type is the Z3 CE solver and its socket carries
     * the stub model extractor; everything else stays inert (never launched). The stub is a
     * {@link Proxy} because {@code SMTSolver.start} is declared with the package-private
     * {@code SolverTimeout}, so the interface cannot be implemented in this module.
     */
    private static SMTSolver stubSolver(ModelExtractor extractor) {
        AbstractSolverSocket socket = new AbstractSolverSocket("z3-ce", extractor) {
            @Override
            public void messageIncoming(de.uka.ilkd.key.smt.communication.Pipe pipe, String msg) {
            }

            @Override
            public AbstractSolverSocket copy() {
                return this;
            }
        };
        return (SMTSolver) Proxy.newProxyInstance(SMTSolver.class.getClassLoader(),
            new Class<?>[] { SMTSolver.class },
            (proxy, method, args) -> switch (method.getName()) {
                case "getType" -> SolverTypes.Z3_CE_SOLVER;
                case "getSocket" -> socket;
                case "name" -> "z3-ce (stub)";
                default -> defaultValue(method.getReturnType());
            });
    }

    /** The inert default answer of the stub solver for the given return type. */
    private static Object defaultValue(Class<?> type) {
        if (type == boolean.class) {
            return false;
        }
        if (type == int.class) {
            return 0;
        }
        if (type == long.class) {
            return 0L;
        }
        return null;
    }

    // ------------------------------------------------------------------ tree helpers

    private static List<String> rootChildLabels(CETreeF ceTree) {
        List<String> labels = new ArrayList<>();
        for (TreeItem<String> child : ceTree.getTreeComponent().getRoot().getChildren()) {
            labels.add(child.getValue());
        }
        return labels;
    }

    private static TreeItem<String> rootChild(CETreeF ceTree, int index) {
        return ceTree.getTreeComponent().getRoot().getChildren().get(index);
    }

    private static @Nullable TreeItem<String> child(TreeItem<String> parent, String label) {
        for (TreeItem<String> c : parent.getChildren()) {
            if (label.equals(c.getValue())) {
                return c;
            }
        }
        return null;
    }

    private static List<String> labels(TreeItem<String> item) {
        List<String> labels = new ArrayList<>();
        for (TreeItem<String> c : item.getChildren()) {
            labels.add(c.getValue());
        }
        return labels;
    }

    private static List<String> tabTitles(InformationWindowF window) {
        List<String> titles = new ArrayList<>();
        TabPane tabs = (TabPane) window.getScene().getRoot();
        for (Tab tab : tabs.getTabs()) {
            titles.add(tab.getText());
        }
        return titles;
    }

    private static <T extends Node> void collect(Class<T> type, @Nullable Node root,
            List<T> out) {
        if (root == null) {
            return;
        }
        if (type.isInstance(root)) {
            out.add(type.cast(root));
        }
        if (root instanceof Parent parent) {
            for (Node child : parent.getChildrenUnmodifiable()) {
                collect(type, child, out);
            }
        }
    }

    private static void check(boolean condition, String what) {
        if (!condition) {
            throw new AssertionError("TestGen verify: " + what + " — failed");
        }
    }

    /** A no-op log sink for the stop-flag task (the pipeline is never started). */
    private static final class RecordingSink implements LogSinkF {
        @Override
        public void writeln(String message) {
        }
    }
}
