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
import javafx.scene.control.MenuButton;
import javafx.scene.control.MenuItem;
import javafx.scene.control.Tooltip;
import javafx.scene.input.KeyCombination;
import javafx.stage.Stage;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
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
 * (Ctrl+T for the {@code TestGenMacro}) and the {@code TestgenOptionsPanel} settings provider; it
 * also implements {@code KeyboardShortcuts} and {@code Startup} and registers selection/Z3
 * listeners so the actions are only enabled on an open proof with the Z3 CE solver installed.
 * <p>
 * The FX port implements the {@link KeYGuiExtensionF} SPI through three capabilities: the
 * settings entry ({@link KeYGuiExtensionF.SettingsF} → {@link TestgenSettingsProviderF}, a
 * reflective {@code SettingsProviderF} proxy), the main-menu entry
 * ({@link KeYGuiExtensionF.MainMenuF} → the "Test Case Generation" menu with the two items of the
 * Swing extension menu, the generate item carrying the SHORTCUT+T accelerator that replaces the
 * Swing {@code KeyStrokeSettings.defineDefault} default) and the status line
 * ({@link KeYGuiExtensionF.StatusLineF}): the same two items inside a {@link MenuButton} plus the
 * two plain action buttons of the Swing toolbar. The long-running generation and the
 * counterexample search run off the FX thread in {@link TestGenerationTaskF} /
 * {@link CounterExampleTaskF} and report into the {@link TestGenResultsDialogF} /
 * {@link CounterExampleResultsDialogF}.
 * <p>
 * <b>KNOWN-SIMPLIFIED (capability reduction):</b> the Swing extension also implements
 * {@code Toolbar} and {@code Startup}, mirrored by the FX SPI as {@code ToolbarF} and
 * {@code StartupF}. The two toolbar actions are expressed through the two plain buttons of the
 * status-line slot (a real {@code ToolbarF} layout is not needed for two buttons, and plain
 * {@code Button}s stay constructible without the FX toolkit, which keeps the headless unit tests
 * toolkit-free), and the {@code StartupF} init hook is not implemented — the window is captured
 * lazily through the settings panel instead (next block). The menu slot is implemented in full:
 * unlike the initial revision, which could not name {@code MainWindowF}/{@code KeYMediatorF} in
 * SPI signatures (javac failed completing {@code MainWindowF} while {@code key.core} was missing
 * from the compile classpath), this module now declares {@code :key.core} like the other keyext
 * FX ports; every runtime window reference remains a plain {@code Object} resolved through
 * {@link TestgenReflectionF}.
 * <p>
 * <b>KNOWN-SIMPLIFIED (lazy window/mediator capture):</b> {@link KeYGuiExtensionF.StatusLineF}
 * does not receive the main window, and no {@code StartupF} hook is implemented, so the port
 * captures the window through the one SPI surface that does pass it — the settings panel
 * ({@link TestgenSettingsProviderF}, whose {@code getPanel/apply} forward the window to
 * {@link #captureWindow(Object)}) — and wires the enablement listeners on that first capture.
 * Until then the buttons stay clickable and validate on click (the run dialogs log the "open the
 * settings dialog once" hint instead of crashing), which mirrors the Swing actions' on-click
 * guards.
 */
@KeYGuiExtensionF.Info(name = "Test case generation", experimental = false,
    description = "key.testgen (JavaFX port): generate JUnit test cases from the current proof, "
        + "or search for a counterexample, using the Z3 CE solver.")
@NullMarked
public final class TestgenExtensionF
        implements KeYGuiExtensionF, KeYGuiExtensionF.SettingsF, KeYGuiExtensionF.StatusLineF,
        KeYGuiExtensionF.MainMenuF {

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
     * every created "Generate Testcases..." item (status MenuButton + main menu), for enablement.
     */
    private final List<MenuItem> generateItems = new ArrayList<>();

    /**
     * every created "Search for Counterexample" item (status MenuButton + main menu), for
     * enablement.
     */
    private final List<MenuItem> counterExampleItems = new ArrayList<>();

    /** main-menu: the "Test Case Generation" menu ({@link KeYGuiExtensionF.MainMenuF}). */
    private @Nullable Menu menu;

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
        // main menu ("Test Case Generation", see getMenus) and in the JToolBar. The FX port
        // expresses the Swing toolbar through this status-line slot (KNOWN-SIMPLIFIED, class
        // comment): the "Test Case Generation" MenuButton re-exposes the two menu items for
        // quick access, the two plain buttons mirror the toolbar.
        if (menuButton == null) {
            MenuButton anchor = new MenuButton(MENU_LABEL);
            // no accelerator here — the SHORTCUT+T binding lives on the main-menu generate
            // item (getMenus) so the two surfaces do not double-fire it
            anchor.getItems().addAll(makeGenerateItem(anchor), makeCounterExampleItem(anchor));

            // Swing TestGenerationAction/CounterExampleAction SMALL_ICONs (FontAwesome)
            Button generate = new Button(NAME_GENERATE, new FontIcon(FontAwesomeSolid.FLASK));
            generate.setTooltip(new Tooltip(TOOLTIP_GENERATE));
            generate.setOnAction(e -> generateTestcases(generate));
            Button counterExample = new Button(NAME_COUNTEREXAMPLE,
                new FontIcon(FontAwesomeSolid.EXCLAMATION_TRIANGLE));
            counterExample.setTooltip(new Tooltip(TOOLTIP_COUNTEREXAMPLE));
            counterExample.setOnAction(e -> searchCounterExample(counterExample));

            menuButton = anchor;
            generateButton = generate;
            counterExampleButton = counterExample;
        }
        return List.of(menuButton, generateButton, counterExampleButton);
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
            // KeyStrokeSettings.defineDefault; the FX SPI has no keyboard-shortcut capability,
            // so the accelerator lives on the menu item. KNOWN-SIMPLIFIED: the shortcut moves
            // from the TestGen strategy macro (term context menu in Swing) to the menu item —
            // the FX app has no macro-keybinding slot yet.
            MenuItem generate = makeGenerateItem(null);
            generate.setAccelerator(KeyCombination.keyCombination("SHORTCUT+T"));
            m.getItems().addAll(generate, makeCounterExampleItem(null));
            menu = m;
        }
        return List.of(menu);
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
