/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.testgen.fx;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.lang.reflect.Proxy;
import java.util.ArrayList;
import java.util.List;
import javafx.application.Platform;
import javafx.beans.property.ReadOnlyBooleanProperty;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Control;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.Tooltip;
import javafx.stage.Stage;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.gui.fx.keyshortcuts.KeyStrokeManagerF;
import de.uka.ilkd.key.gui.fx.settings.SettingsProviderF;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.kordamp.ikonli.fontawesome6.FontAwesomeSolid;
import org.kordamp.ikonli.javafx.FontIcon;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Test-case generation extension, JavaFX port of
 * {@code de.uka.ilkd.key.gui.testgen.TestgenExtension} (Swing TestgenExtension.java:24-73). The
 * Swing original contributes two {@code Action}s ("Search for Counterexample", "Generate
 * Testcases...") to the main menu (grouped by the Swing facade into an "Extensions" menu), a
 * {@code JToolBar} with the same two actions, a {@code KeyStrokeSettings.defineDefault} shortcut
 * (Ctrl+Shift+T ({@code MULTI_KEY_MASK}) for the {@code TestGenMacro}) and the {@code
 * TestgenOptionsPanel} settings provider; it
 * also implements {@code KeyboardShortcuts} and {@code Startup} and registers selection/Z3
 * listeners so the actions are only enabled on an open proof with the Z3 CE solver installed.
 * <p>
 * The FX port implements the {@link KeYGuiExtensionF} SPI through four capabilities: the settings
 * entry ({@link KeYGuiExtensionF.SettingsF} → {@link TestgenSettingsProviderF}, a reflective
 * {@code SettingsProviderF} proxy), the main-menu entry ({@link KeYGuiExtensionF.MainMenuF} → the
 * "Test Case Generation" menu with the two items of the Swing extension menu), the toolbar
 * ({@link KeYGuiExtensionF.ToolbarF} → the two plain action buttons of the Swing {@code JToolBar}
 * in the host's extension toolbar) and the startup hook ({@link KeYGuiExtensionF.StartupF} →
 * {@link #init(MainWindowF, KeYMediatorF)}, which hands the window to the extension at app
 * startup exactly like the Swing {@code Startup} hook does — WP-7). The long-running generation
 * and the counterexample search run off the FX thread in {@link TestGenerationTaskF} /
 * {@link CounterExampleTaskF} and report into the {@link TestGenResultsDialogF} /
 * {@link CounterExampleResultsDialogF}.
 * <p>
 * WP-7 closes the former capability reduction: the extension now implements {@code ToolbarF} and
 * {@code StartupF} like its Swing original. The status-line stand-in (the "Test Case Generation"
 * {@code MenuButton} re-exposing the two menu items) is dropped with it — it existed only because
 * the toolbar slot was missing, and Swing parity is exactly menu + toolbar. The window still
 * arrives through the settings panel as a fallback (the reflective settings proxy forwards it to
 * {@link #captureWindow(Object)}); with the {@code StartupF} hook in place it arrives at startup,
 * so the enablement wiring (selection, auto-mode and SMT-settings listeners, the FX equivalent of
 * the Swing action-infrastructure updates) runs from the start instead of on the first settings
 * dialog visit.
 */
@KeYGuiExtensionF.Info(name = "Test case generation", experimental = false,
    description = "key.testgen (JavaFX port): generate JUnit test cases from the current proof, "
        + "or search for a counterexample, using the Z3 CE solver.")
@NullMarked
public final class TestgenExtensionF
        implements KeYGuiExtensionF, KeYGuiExtensionF.SettingsF, KeYGuiExtensionF.ToolbarF,
        KeYGuiExtensionF.StartupF, KeYGuiExtensionF.MainMenuF {

    private static final Logger LOGGER = LoggerFactory.getLogger(TestgenExtensionF.class);

    /** Label of the extension's main-menu area (the Swing "Extensions" menu label equivalent). */
    private static final String MENU_LABEL = "Test Case Generation";

    /** Swing TestGenerationAction.NAME. */
    private static final String NAME_GENERATE = "Generate Testcases...";

    /** Swing CounterExampleAction.NAME. */
    private static final String NAME_COUNTEREXAMPLE = "Search for Counterexample";

    /**
     * action id of the TestGenMacro in the shared keystroke settings (the macro's real FQN —
     * the Swing {@code KeyStrokeSettings.defineDefault} id, see {@code KeyStrokeManagerF}).
     */
    private static final String TESTGEN_MACRO_ACTION_ID =
        "de.uka.ilkd.key.testgen.macros.TestGenMacro";

    /** Swing TestGenerationAction.TOOLTIP. */
    private static final String TOOLTIP_GENERATE = "Generate test cases for open goals";

    /** Swing CounterExampleAction.TOOLTIP. */
    private static final String TOOLTIP_COUNTEREXAMPLE =
        "Search for a counterexample for the selected goal";

    /** the TestgenOptionsPanel port; a reflective {@code SettingsProviderF} proxy (see class). */
    private final SettingsProviderF settingsProvider = TestgenSettingsProviderF.create(this);

    /** toolbar: the two plain buttons of the Swing JToolBar (Swing TestgenExtension.getToolbar). */
    private @Nullable Button generateButton;
    private @Nullable Button counterExampleButton;

    /** every created "Generate Testcases..." main-menu item, for enablement. */
    private final List<MenuItem> generateItems = new ArrayList<>();

    /** every created "Search for Counterexample" main-menu item, for enablement. */
    private final List<MenuItem> counterExampleItems = new ArrayList<>();

    /** main-menu: the "Test Case Generation" menu ({@link KeYGuiExtensionF.MainMenuF}). */
    private @Nullable Menu menu;

    /**
     * the main window, captured at startup through the {@code StartupF}/{@code ToolbarF} hooks
     * (WP-7) or as a fallback through the settings panel (the reflective settings proxy): it was
     * {@code null} until the user opened the settings dialog before WP-7. Kept as a plain
     * {@code Object} — {@code MainWindowF} is not nameable in this module.
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

    // ------------------------------------------------------------------ ToolbarF

    @Override
    public List<Control> getToolbarControls(MainWindowF window, KeYMediatorF mediator) {
        // WP-7 — Swing TestgenExtension.getToolbar (TestgenExtension.java:55-61): the JToolBar
        // with the two actions; the FX host appends the contributed controls to its single
        // extension toolbar (MainWindowF.buildTop). The window also arrives here (the toolbar is
        // built after the mediator is set), so the enablement wiring starts like through the
        // StartupF hook below.
        if (window != null) {
            captureWindow(window);
        }
        if (generateButton == null) {
            // Swing TestGenerationAction/CounterExampleAction SMALL_ICONs (FontAwesome);
            // reviewer request: icon-only toolbar controls
            Button generate = new Button(null, new FontIcon(FontAwesomeSolid.FLASK));
            generate.setAccessibleText(NAME_GENERATE);
            generate.setTooltip(new Tooltip(TOOLTIP_GENERATE));
            generate.setOnAction(e -> generateTestcases(generate));
            Button counterExample = new Button(null,
                new FontIcon(FontAwesomeSolid.EXCLAMATION_TRIANGLE));
            counterExample.setAccessibleText(NAME_COUNTEREXAMPLE);
            counterExample.setTooltip(new Tooltip(TOOLTIP_COUNTEREXAMPLE));
            counterExample.setOnAction(e -> searchCounterExample(counterExample));
            generateButton = generate;
            counterExampleButton = counterExample;
        }
        refresh();
        return List.of(generateButton, counterExampleButton);
    }

    // ------------------------------------------------------------------ StartupF

    @Override
    public void init(MainWindowF window, KeYMediatorF mediator) {
        // WP-7 — Swing TestgenExtension.init (TestgenExtension.java:48-53): the Startup hook
        // hands the window to the extension at app startup. The window capture enables the
        // enablement listeners (captureWindow) instead of the former lazy capture through the
        // settings panel.
        captureWindow(window);
    }

    // ------------------------------------------------------------------ MainMenuF

    @Override
    public List<Menu> getMenus(MainWindowF window, KeYMediatorF mediator) {
        // extension: MP9.5 — Swing TestgenExtension.getMainMenuActions
        // (TestgenExtension.java:43-51): the two actions, grouped by the Swing facade into an
        // "Extensions" menu; the FX SPI contributes whole menus, so they live in a new
        // "Test Case Generation" menu (the five built-in menu bars and their item sets stay
        // untouched — key.fx.verify.menuparity keeps asserting 16/24/12/7/5).
        if (menu == null) {
            Menu m = new Menu(MENU_LABEL);
            // Swing TestgenExtension.java:51-52 registers the TestGenMacro default shortcut via
            // KeyStrokeSettings.defineDefault (MULTI_KEY_MASK = Ctrl+Shift+T); the FX
            // counterpart is the shared KeyStrokeManagerF default, which also drives the
            // accelerator of the macro item in the proof macro menus
            // (ProofMacroMenuF.itemFor). The main-menu item carries the manager binding and is
            // registered for later rebindings (KeyStrokeManager.register).
            KeyStrokeManagerF manager = KeyStrokeManagerF.getInstance();
            MenuItem generate = makeGenerateItem(null);
            manager.binding(TESTGEN_MACRO_ACTION_ID).ifPresent(generate::setAccelerator);
            manager.register(generate, TESTGEN_MACRO_ACTION_ID);
            m.getItems().addAll(generate, makeCounterExampleItem(null));
            menu = m;
        }
        return List.of(menu);
    }

    // ------------------------------------------------------------------ window capture

    /**
     * Hands the main window to the extension — called from the {@code StartupF}/{@code ToolbarF}
     * hooks (WP-7) and, as a fallback, from the settings panel (the
     * {@code SettingsProviderF} panel/apply forwarded by {@link TestgenSettingsProviderF}).
     * Wires the enablement listeners once (the reflection-only counterpart of the Swing
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
    private void generateTestcases(@Nullable Node source) {
        Object captured = window;
        if (captured == null) {
            LOGGER.warn("Testgen extension not connected to a main window yet - the run dialog "
                + "will only log the hint; open the application settings (TestGen page) once");
        }
        new TestGenResultsDialogF(captured, stageOf(source)).showAndStart();
    }

    /** Opens the counterexample search run dialog and starts the search. */
    private void searchCounterExample(@Nullable Node source) {
        Object captured = window;
        if (captured == null) {
            LOGGER.warn("Testgen extension not connected to a main window yet - the run dialog "
                + "will only log the hint; open the application settings (TestGen page) once");
        }
        new CounterExampleResultsDialogF(captured, stageOf(source)).showAndStart();
    }

    /**
     * The {@link Stage} owning the given node (the toolbar button lives in the main window's
     * scene; main-menu {@link MenuItem}s have none and return {@code null}), used as the run
     * dialogs' owner.
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
     * Re-computes the enablement of the toolbar buttons and main-menu items: like the Swing
     * actions the extension is enabled only when Z3 CE is installed, a proof is selected and no
     * auto-mode / generation run is active (Swing TestGenerationAction.checkZ3CE,
     * TestGenerationAction.java:101-111); the counterexample action additionally requires the
     * selected node to be an open leaf (CounterExampleAction.selectedNodeChanged,
     * CounterExampleAction.java:67-84). The selection and SMT-settings events can fire on any
     * thread, so the refresh is marshalled to the FX thread.
     * <p>
     * Without a captured window the controls stay enabled and the run dialogs validate on click
     * (the fallback capture through the settings panel, see the class comment).
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
        for (MenuItem item : generateItems) {
            item.setDisable(!generateEnabled);
        }
        for (MenuItem item : counterExampleItems) {
            item.setDisable(!counterExampleEnabled);
        }
        Button generate = generateButton;
        if (generate != null) {
            generate.setDisable(!generateEnabled);
        }
        Button counterExample = counterExampleButton;
        if (counterExample != null) {
            counterExample.setDisable(!counterExampleEnabled);
        }
    }

    // ------------------------------------------------------------------ helpers

    /**
     * Creates one "Generate Testcases..." item for the given surface ({@code null} source for
     * the main-menu entry, whose {@link MenuItem} is not a {@link Node}), carrying the
     * FontAwesome glyph of the Swing {@code TestGenerationAction} SMALL_ICON; tracked for
     * enablement ({@link #setEnabled}).
     */
    private MenuItem makeGenerateItem(@Nullable Node source) {
        MenuItem item = new MenuItem(NAME_GENERATE);
        item.setGraphic(new FontIcon(FontAwesomeSolid.FLASK));
        item.setOnAction(e -> generateTestcases(source));
        generateItems.add(item);
        return item;
    }

    /**
     * Creates one "Search for Counterexample" item for the given surface (see
     * {@link #makeGenerateItem}), carrying the FontAwesome glyph of the Swing
     * {@code CounterExampleAction} SMALL_ICON; tracked for enablement.
     */
    private MenuItem makeCounterExampleItem(@Nullable Node source) {
        MenuItem item = new MenuItem(NAME_COUNTEREXAMPLE);
        item.setGraphic(new FontIcon(FontAwesomeSolid.EXCLAMATION_TRIANGLE));
        item.setOnAction(e -> searchCounterExample(source));
        counterExampleItems.add(item);
        return item;
    }
}
