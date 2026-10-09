/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.testgen.fx;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.lang.reflect.Proxy;
import java.util.List;
import javafx.application.Platform;
import javafx.beans.property.ReadOnlyBooleanProperty;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Control;
import javafx.scene.control.MenuButton;
import javafx.scene.control.MenuItem;
import javafx.scene.control.Tooltip;
import javafx.scene.input.KeyCombination;
import javafx.stage.Stage;

import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.gui.fx.settings.SettingsProviderF;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Test-case generation extension, JavaFX port of
 * {@code de.uka.ilkd.key.gui.testgen.TestgenExtension} (Swing TestgenExtension.java:24-73). The
 * Swing original contributes two {@code Action}s ("Search for Counterexample", "Generate
 * Testcases...") to the main menu (grouped by the Swing facade into an "Extensions" menu), a
 * {@code JToolBar} with the same two actions, a {@code KeyStrokeSettings.defineDefault} shortcut
 * (Ctrl+T for the {@code TestGenMacro}) and the {@code TestgenOptionsPanel} settings provider; it
 * also implements {@code KeyboardShortcuts} and {@code Startup} and registers selection/Z3
 * listeners so the actions are only enabled on an open proof with the Z3 CE solver installed.
 * <p>
 * The FX port implements the {@link KeYGuiExtensionF} SPI through the two capabilities that are
 * compilable in this module (see below): the settings entry
 * ({@link KeYGuiExtensionF.SettingsF} → {@link TestgenSettingsProviderF}, a reflective
 * {@code SettingsProviderF} proxy) and the status line ({@link KeYGuiExtensionF.StatusLineF}): a
 * "Test Case Generation" {@link MenuButton} carrying the two menu items of the Swing extension
 * menu (incl. the SHORTCUT+T accelerator that replaces the Swing
 * {@code KeyStrokeSettings.defineDefault} default) and the two plain action buttons of the Swing
 * toolbar. The long-running generation and the counterexample search run off the FX thread in
 * {@link TestGenerationTaskF} / {@link CounterExampleTaskF} and report into the
 * {@link TestGenResultsDialogF} / {@link CounterExampleResultsDialogF}.
 * <p>
 * <b>KNOWN-SIMPLIFIED (capability reduction):</b> the Swing extension implements
 * {@code MainMenu}, {@code Toolbar}, {@code KeyboardShortcuts} and {@code Startup}; the FX SPI
 * mirrors those as {@link KeYGuiExtensionF.MainMenuF}, {@code ToolbarF} and {@code StartupF},
 * whose method signatures reference {@code MainWindowF}/{@code KeYMediatorF}. Any use of those
 * types in this module forces javac to complete the {@code MainWindowF} class file, which fails
 * ("Cannot attach type annotations ... to MainWindowF.lastEnvironment: class file for
 * de.uka.ilkd.key.control.KeYEnvironment not found" — key.core is not on the frozen compile
 * classpath); the menu and toolbar slots are therefore merged into a single status-line slot, and
 * every window reference is a plain {@code Object} resolved through {@link TestgenReflectionF}.
 * <p>
 * <b>KNOWN-SIMPLIFIED (lazy window/mediator capture):</b> {@link KeYGuiExtensionF.StatusLineF}
 * does not receive the main window, and the {@code StartupF} init hook that the built-in
 * status-line extensions use to bind the mediator is compile-impossible in this module (see
 * above). The port therefore captures the window through the one SPI surface that does pass it —
 * the settings panel ({@link TestgenSettingsProviderF}, whose {@code getPanel/apply} forward the
 * window to {@link #captureWindow(Object)}) — and wires the enablement listeners on that first
 * capture. Until then the buttons stay clickable and validate on click (the run dialogs log the
 * "open the settings dialog once" hint instead of crashing), which mirrors the Swing actions'
 * on-click guards.
 */
@KeYGuiExtensionF.Info(name = "Test case generation", experimental = false,
    description = "key.testgen (JavaFX port): generate JUnit test cases from the current proof, "
        + "or search for a counterexample, using the Z3 CE solver.")
@NullMarked
public final class TestgenExtensionF
        implements KeYGuiExtensionF, KeYGuiExtensionF.SettingsF, KeYGuiExtensionF.StatusLineF {

    private static final Logger LOGGER = LoggerFactory.getLogger(TestgenExtensionF.class);

    /** Label of the status-line extension area (the Swing "Extensions" menu label equivalent). */
    private static final String MENU_LABEL = "Test Case Generation";

    /** Swing TestGenerationAction.NAME. */
    private static final String NAME_GENERATE = "Generate Testcases...";

    /** Swing CounterExampleAction.NAME. */
    private static final String NAME_COUNTEREXAMPLE = "Search for Counterexample";

    /** Swing TestGenerationAction.TOOLTIP. */
    private static final String TOOLTIP_GENERATE = "Generate test cases for open goals";

    /** Swing CounterExampleAction.TOOLTIP. */
    private static final String TOOLTIP_COUNTEREXAMPLE =
        "Search for a counterexample for the selected goal";

    /** the TestgenOptionsPanel port; a reflective {@code SettingsProviderF} proxy (see class). */
    private final SettingsProviderF settingsProvider = TestgenSettingsProviderF.create(this);

    /** status-line: the anchor menu button with the two extension-menu items. */
    private @Nullable MenuButton menuButton;

    /** status-line: the two plain toolbar buttons (Swing JToolBar entries). */
    private @Nullable Button generateButton;
    private @Nullable Button counterExampleButton;

    /**
     * the main window, captured lazily through the settings panel (see the class comment for the
     * {@code KNOWN-SIMPLIFIED} reasoning): {@code null} until the user opens the settings dialog.
     * Kept as a plain {@code Object} — {@code MainWindowF} is not nameable in this module.
     */
    private @Nullable Object window;

    /** whether the enablement listeners are wired (once per captured window). */
    private boolean initialized;

    // ------------------------------------------------------------------ SettingsF

    @Override
    public SettingsProviderF getSettings() {
        // extension: MP9.5 — Swing TestgenExtension.java:70-72: the TestgenOptionsPanel.
        return settingsProvider;
    }

    // ------------------------------------------------------------------ StatusLineF

    @Override
    public List<Control> getStatusLineControls() {
        // extension: MP9.5 — Swing TestgenExtension.java:43-61: the two actions live in the
        // main menu (grouped into the "Extensions" menu by the Swing facade) and in a JToolBar.
        // The FX SPI contributes whole menus (KeYGuiExtensionF.MainMenuF) or toolbar controls
        // (ToolbarF); both slots are compile-impossible here (see the class comment), so both
        // contributions are merged into one status-line slot: the "Test Case Generation"
        // MenuButton carries the two menu items, the two plain buttons mirror the toolbar.
        if (menuButton == null) {
            MenuButton anchor = new MenuButton(MENU_LABEL);
            MenuItem generateItem = menuItem(NAME_GENERATE, () -> generateTestcases(anchor));
            // The Swing original registers the default shortcut on the TestGenMacro
            // (TestgenExtension.java:51-52 via KeyStrokeSettings.defineDefault). The FX SPI has
            // no keyboard-shortcut capability, so the accelerator is attached to the menu item
            // instead.
            // KNOWN-SIMPLIFIED: shortcut moved from the TestGen strategy macro (term context
            // menu in Swing) to the "Generate Testcases..." menu item; the FX app has no
            // macro-keybinding slot yet.
            generateItem.setAccelerator(KeyCombination.keyCombination("SHORTCUT+T"));
            MenuItem counterExampleItem =
                menuItem(NAME_COUNTEREXAMPLE, () -> searchCounterExample(anchor));
            anchor.getItems().addAll(generateItem, counterExampleItem);

            Button generate = new Button(NAME_GENERATE);
            generate.setTooltip(new Tooltip(TOOLTIP_GENERATE));
            generate.setOnAction(e -> generateTestcases(generate));
            Button counterExample = new Button(NAME_COUNTEREXAMPLE);
            counterExample.setTooltip(new Tooltip(TOOLTIP_COUNTEREXAMPLE));
            counterExample.setOnAction(e -> searchCounterExample(counterExample));

            menuButton = anchor;
            generateButton = generate;
            counterExampleButton = counterExample;
        }
        return List.of(menuButton, generateButton, counterExampleButton);
    }

    // ------------------------------------------------------------------ window capture

    /**
     * Hands the main window to the extension — the only SPI surface of this module that receives
     * it (the {@code SettingsProviderF} panel/apply, forwarded by
     * {@link TestgenSettingsProviderF}).
     * Used to bind the enablement listeners once (the reflection-only counterpart of the Swing
     * {@code Startup} hook).
     *
     * @param window the main window handed in by the settings dialog
     */
    void captureWindow(Object window) {
        this.window = window;
        if (initialized) {
            return;
        }
        initialized = true;
        Object mediator = TestgenReflectionF.mediatorOf(window);
        if (mediator != null) {
            wireSelectionListener(mediator);
            wireAutoModeListener(mediator);
            wireSmtSettingsListener();
        }
        refresh();
    }

    // ------------------------------------------------------------------ run dialogs

    /** Opens the test-suite generation run dialog and starts the generation. */
    private void generateTestcases(Node source) {
        Object captured = window;
        if (captured == null) {
            LOGGER.warn("Testgen extension not connected to a main window yet - the run dialog "
                + "will only log the hint; open the application settings (TestGen page) once");
        }
        new TestGenResultsDialogF(captured, stageOf(source)).showAndStart();
    }

    /** Opens the counterexample search run dialog and starts the search. */
    private void searchCounterExample(Node source) {
        Object captured = window;
        if (captured == null) {
            LOGGER.warn("Testgen extension not connected to a main window yet - the run dialog "
                + "will only log the hint; open the application settings (TestGen page) once");
        }
        new CounterExampleResultsDialogF(captured, stageOf(source)).showAndStart();
    }

    /**
     * The {@link Stage} owning the given node (the status-line controls live in the main
     * window's scene), used as the run dialogs' owner.
     */
    private static @Nullable Stage stageOf(@Nullable Node source) {
        if (source == null) {
            return null;
        }
        Scene scene = source.getScene();
        return scene != null && scene.getWindow() instanceof Stage stage ? stage : null;
    }

    // ------------------------------------------------------------------ enablement

    /**
     * Registers the selection listener of the Swing actions through a reflective proxy: the
     * {@code KeYSelectionListener} interface is typed with key.core classes (Node/Proof), so it
     * cannot be implemented at compile time in this module.
     */
    private void wireSelectionListener(Object mediator) {
        try {
            Object selectionModel =
                mediator.getClass().getMethod("getSelectionModel").invoke(mediator);
            Class<?> listenerInterface =
                Class.forName("de.uka.ilkd.key.core.fx.KeYSelectionListener");
            Object listener = Proxy.newProxyInstance(listenerInterface.getClassLoader(),
                new Class<?>[] { listenerInterface }, (proxy, method, args) -> {
                    switch (method.getName()) {
                        case "selectedNodeChanged", "selectedProofChanged" -> refresh();
                        case "equals" -> {
                            return args != null && args.length == 1 && args[0] == proxy;
                        }
                        case "hashCode" -> {
                            return System.identityHashCode(proxy);
                        }
                        case "toString" -> {
                            return "TestgenSelectionListener(proxy)";
                        }
                        default -> {
                        }
                    }
                    return null;
                });
            selectionModel.getClass().getMethod("addKeYSelectionListener", listenerInterface)
                    .invoke(selectionModel, listener);
        } catch (ReflectiveOperationException | RuntimeException e) {
            LOGGER.warn("Could not register the KeYSelectionListener of the testgen extension", e);
        }
    }

    /** Binds the enablement to the observable auto-mode state of the FX mediator. */
    private void wireAutoModeListener(Object mediator) {
        if (TestgenReflectionF.autoModePropertyOf(mediator) instanceof ReadOnlyBooleanProperty p) {
            p.addListener((obs, oldValue, value) -> refresh());
        }
    }

    /**
     * Registers a listener on the global SMT settings so the extension reacts when the Z3 solver
     * installation changes (Swing TestGenerationAction.checkZ3CE,
     * TestGenerationAction.java:101-111 via {@code ProofIndependentSettings}).
     */
    private void wireSmtSettingsListener() {
        try {
            Object defaultInstance = Class
                    .forName("de.uka.ilkd.key.settings.ProofIndependentSettings")
                    .getField("DEFAULT_INSTANCE").get(null);
            Object smtSettings = defaultInstance.getClass().getMethod("getSMTSettings")
                    .invoke(defaultInstance);
            smtSettings.getClass().getMethod("addPropertyChangeListener",
                PropertyChangeListener.class)
                    .invoke(smtSettings, (PropertyChangeListener) this::handleSMTSettingsChanged);
        } catch (ReflectiveOperationException | RuntimeException e) {
            LOGGER.warn("Could not register the SMT-settings listener of the testgen extension",
                e);
        }
    }

    private void handleSMTSettingsChanged(PropertyChangeEvent evt) {
        refresh();
    }

    /**
     * Re-computes the enablement of the status-line controls: like the Swing actions the
     * extension is enabled only when Z3 CE is installed, a proof is selected and no auto-mode /
     * generation run is active (Swing TestGenerationAction.checkZ3CE,
     * TestGenerationAction.java:101-111); the counterexample action additionally requires the
     * selected node to be an open leaf (CounterExampleAction.selectedNodeChanged,
     * CounterExampleAction.java:67-84). The selection and SMT-settings events can fire on any
     * thread, so the refresh is marshalled to the FX thread.
     * <p>
     * Without a captured window the controls stay enabled and the run dialogs validate on click
     * (the class comment's {@code KNOWN-SIMPLIFIED} lazy capture).
     */
    private void refresh() {
        Object connected = window;
        if (connected == null) {
            return;
        }
        if (!Platform.isFxApplicationThread()) {
            Platform.runLater(this::refresh);
            return;
        }
        Object mediator = TestgenReflectionF.mediatorOf(connected);
        boolean z3Available = TestgenReflectionF.z3CeInstalled();
        boolean autoMode = false;
        if (mediator != null
                && TestgenReflectionF
                        .autoModePropertyOf(mediator) instanceof ReadOnlyBooleanProperty p) {
            autoMode = p.get();
        }
        boolean proofLoaded = mediator != null && TestgenReflectionF.proofOf(mediator) != null;
        boolean generateEnabled = z3Available && !autoMode && proofLoaded;
        boolean counterExampleEnabled = generateEnabled && mediator != null
                && TestgenReflectionF.isOpenLeaf(TestgenReflectionF.nodeOf(mediator));
        setEnabled(generateEnabled, counterExampleEnabled);
    }

    private void setEnabled(boolean generateEnabled, boolean counterExampleEnabled) {
        MenuButton anchor = menuButton;
        Button generate = generateButton;
        Button counterExample = counterExampleButton;
        if (anchor != null) {
            for (MenuItem item : anchor.getItems()) {
                boolean isGenerate = NAME_GENERATE.equals(item.getText());
                item.setDisable(isGenerate ? !generateEnabled : !counterExampleEnabled);
            }
        }
        if (generate != null) {
            generate.setDisable(!generateEnabled);
        }
        if (counterExample != null) {
            counterExample.setDisable(!counterExampleEnabled);
        }
    }

    // ------------------------------------------------------------------ helpers

    private static MenuItem menuItem(String text, Runnable action) {
        MenuItem item = new MenuItem(text);
        item.setOnAction(e -> action.run());
        return item;
    }
}
