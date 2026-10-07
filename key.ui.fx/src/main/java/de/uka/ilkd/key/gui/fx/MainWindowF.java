/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx;

import java.io.IOException;
import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import javafx.application.Platform;
import javafx.concurrent.Task;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.control.CheckMenuItem;
import javafx.scene.control.Label;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuBar;
import javafx.scene.control.MenuItem;
import javafx.scene.control.RadioMenuItem;
import javafx.scene.control.SeparatorMenuItem;
import javafx.scene.control.ToggleGroup;
import javafx.scene.control.ToolBar;
import javafx.scene.control.Tooltip;
import javafx.scene.image.Image;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyEvent;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.Region;
import javafx.scene.layout.StackPane;
import javafx.scene.layout.VBox;
import javafx.stage.Stage;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.core.fx.KeYSelectionModel;
import de.uka.ilkd.key.gui.fx.configuration.ConfigF;
import de.uka.ilkd.key.gui.fx.docking.DockLayoutStore;
import de.uka.ilkd.key.gui.fx.docking.DockLocation;
import de.uka.ilkd.key.gui.fx.docking.DockWorkspace;
import de.uka.ilkd.key.gui.fx.docking.Dockable;
import de.uka.ilkd.key.gui.fx.docking.SimpleDockable;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF;
import de.uka.ilkd.key.gui.fx.goallist.GoalListViewF;
import de.uka.ilkd.key.gui.fx.infoview.InfoViewF;
import de.uka.ilkd.key.gui.fx.keyshortcuts.KeyStrokeManagerF;
import de.uka.ilkd.key.gui.fx.nodeviews.SequentViewF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF.Kind;
import de.uka.ilkd.key.gui.fx.prooftree.ProofTreeViewF;
import de.uka.ilkd.key.gui.fx.settings.SettingsManagerF;
import de.uka.ilkd.key.gui.fx.settings.ThemeSettingsProviderF;
import de.uka.ilkd.key.gui.fx.strategy.StrategySelectionViewF;
import de.uka.ilkd.key.gui.fx.theme.Theme;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;
import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.KeYResourceManager;

import org.key_project.util.javafx.FxUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The main window of the JavaFX UI, counter-part of {@code de.uka.ilkd.key.gui.MainWindow} in the
 * Swing module {@code key.ui}.
 * <p>
 * Milestone M1: the window hosts the docking workspace (with the default layout of placeholder
 * dockables — the real views arrive in M2), the menu bar and toolbars (actions are progressively
 * wired in M3), a themed status bar, and the notification overlay. The layout persistence
 * ({{@link DockLayoutStore}) mirrors {@code layout.xml} of the Swing UI.
 */
public final class MainWindowF {

    private static final Logger LOGGER = LoggerFactory.getLogger(MainWindowF.class);

    private static final String IMAGE_DIR = "/de/uka/ilkd/key/gui/images/";

    /** Known dockable ids, in the order they appear in the factory-default layout. */
    public static final String ID_LOADED_PROOFS = "loadedProofs";
    public static final String ID_GOAL_LIST = "goalList";
    public static final String ID_PROOF_TREE = "proofTree";
    public static final String ID_INFO_VIEW = "infoView";
    public static final String ID_STRATEGY = "strategySelection";
    public static final String ID_SEQUENT = "sequent";
    public static final String ID_SOURCE_VIEW = "sourceView";

    private final Stage stage;
    private final DockWorkspace workspace = new DockWorkspace();
    private final DockLayoutStore layoutStore;
    private final Map<String, Dockable> dockables = new LinkedHashMap<>();

    private final Label statusLeft = new Label();
    private final Label statusRight = new Label();

    /**
     * The sequent view is the first real view of milestone M2 (currently a spike rendering the
     * printed sequent of the root node of a demo proof, see {@link #startDemoProofLoad()}).
     */
    private final SequentViewF sequentView = new SequentViewF();

    /**
     * The mediator of the window (M2 skeleton): owns the selection model, binds the proof
     * listeners and shares the notation info. The demo load routes the proof through
     * {@code setSelectedProof}, which invokes the mediator's {@code setProof}.
     */
    private final KeYMediatorF mediator = new KeYMediatorF();

    /**
     * The selection model of the window, owned by the mediator.
     */
    private final KeYSelectionModel selectionModel = mediator.getSelectionModel();

    /**
     * The proof tree view (first M2 version): displays the proof of the selection model, node
     * clicks drive the selection.
     */
    private final ProofTreeViewF proofTreeView = new ProofTreeViewF();

    /**
     * The info view (first M2 version): shows the proof-level details (name, file, goal/node/
     * branch counts, closed status) of the selected proof.
     */
    private final InfoViewF infoView = new InfoViewF();

    /**
     * The goal list view (first M2 version): lists the open goals of the selected proof; a click
     * selects the goal.
     */
    private final GoalListViewF goalListView = new GoalListViewF();

    /**
     * The strategy selection view (first M2 version): settings-definition-driven control panel
     * writing through to the selected proof's strategy settings.
     */
    private final StrategySelectionViewF strategyView = new StrategySelectionViewF();

    /**
     * Updates the left status text whenever the selection changes: proof name, closed state or
     * the number of open goals (Swing's status line is message-driven; the proof summary is the
     * persistent M2 content). Marshalled to the FX thread (the mediator's
     * {@code defaultSelection} may fire from the prover thread).
     */
    private final KeYSelectionListener statusSelectionListener = new KeYSelectionListener() {
        @Override
        public void selectedProofChanged(KeYSelectionEvent<Proof> event) {
            updateProofStatus();
        }

        @Override
        public void selectedNodeChanged(KeYSelectionEvent<de.uka.ilkd.key.proof.Node> event) {
            updateProofStatus();
        }
    };

    /**
     * Creates the main window bound to the given stage.
     *
     * @param stage the primary stage of the JavaFX application
     */
    public MainWindowF(Stage stage) {
        this.stage = stage;
        this.layoutStore = new DockLayoutStore(PathConfig.currentPaths.keyConfigDir);
    }

    /**
     * Builds and shows the main window.
     */
    public void initialize() {
        stage.setTitle(KeYResourceManager.getManager().getUserInterfaceTitle());
        setWindowIcons();

        registerSettingsProviders();
        buildDockables();
        workspace.setDefaultLayout(defaultLayout());

        BorderPane root = new BorderPane();
        root.setTop(buildTop());
        StackPane center = new StackPane(workspace.getRoot());
        NotificationManagerF.getInstance().attach(center);
        root.setCenter(center);
        root.setBottom(buildStatusBar());

        Scene scene = new Scene(root, 1100, 800);
        ThemeManager.getInstance().manage(scene);
        // the global action keys of the Swing AutoModeAction (Ctrl+Space starts, Escape stops);
        // an open search bar consumes Escape itself, so it never stops a run while visible
        scene.setOnKeyPressed(this::handleMainWindowKeyPressed);
        stage.setScene(scene);
        stage.show();

        restoreLayout();

        ThemeManager.getInstance().themeProperty().addListener((obs, old, theme) -> updateStatus());
        updateStatus();

        wireSequentView();
        startDemoProofLoad();

        NotificationManagerF.getInstance()
                .notify("KeY (JavaFX) started. Docking layout restored from "
                    + layoutStore.file() + ".");
    }

    /**
     * @return the docking workspace of the main window
     */
    public DockWorkspace getWorkspace() {
        return workspace;
    }

    /**
     * @return the registered dockables (id → dockable)
     */
    public Map<String, Dockable> getDockables() {
        return dockables;
    }

    /**
     * @return the sequent view docked in the main area
     */
    public SequentViewF getSequentView() {
        return sequentView;
    }

    /**
     * @return the selection model of the window
     */
    public KeYSelectionModel getSelectionModel() {
        return selectionModel;
    }

    // ------------------------------------------------------------------
    // sequent view (M2a spike)
    // ------------------------------------------------------------------

    private void wireSequentView() {
        sequentView.attach(selectionModel);
        proofTreeView.attach(selectionModel);
        infoView.attach(selectionModel);
        goalListView.attach(selectionModel);
        strategyView.attach(selectionModel);
        selectionModel.addKeYSelectionListenerChecked(statusSelectionListener);
        sequentView.setOnPosSelected(pos -> {
            if (pos == null) {
                statusRight.setText("");
                return;
            }
            String text = sequentView.getHighlightedText(pos);
            statusRight.setText(text.isBlank() ? String.valueOf(pos) : text);
            LOGGER.info("Clicked sequent position: {}", pos);
        });
    }

    /**
     * Milestone M2a spike affordance: if the system property {@code key.fx.demo.sequent} is set to
     * a {@code .key} file, load it with the core {@link KeYEnvironment} on a background thread and
     * display the root sequent in the sequent view.
     */
    private void startDemoProofLoad() {
        String file = System.getProperty("key.fx.demo.sequent");
        if (file == null || file.isBlank()) {
            return;
        }
        Path location = Path.of(file);
        Task<KeYEnvironment<DefaultUserInterfaceControl>> loadTask = new Task<>() {
            @Override
            protected KeYEnvironment<DefaultUserInterfaceControl> call() throws Exception {
                KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(location);
                if (System.getProperty("key.fx.demo.autoprove") != null) {
                    LOGGER.info("Demo: running auto mode on the loaded proof");
                    env.getProofControl().startAndWaitForAutoMode(env.getLoadedProof());
                    LOGGER.info("Demo: auto mode finished");
                }
                return env;
            }
        };
        loadTask.setOnSucceeded(event -> {
            KeYEnvironment<DefaultUserInterfaceControl> env = loadTask.getValue();
            // the mediator observes the proof control (auto mode state, closed-goal counter);
            // the UI's own listener refreshes the views after interactive auto mode runs
            mediator.attach(env.getProofControl());
            env.getProofControl().addAutoModeListener(autoModeUiListener);
            // route the proof through the selection model: setSelectedProof invokes the
            // mediator's setProof (listener swap, abbreviation rebind, OSS refresh) and then
            // selects the first open goal or a leaf, which the views observe.
            selectionModel.setSelectedProof(env.getLoadedProof());
            String show = System.getProperty("key.fx.show", ID_SEQUENT);
            String target = ID_PROOF_TREE.equalsIgnoreCase(show) ? ID_PROOF_TREE : ID_SEQUENT;
            LOGGER.info("Demo: selecting dockable '{}' (key.fx.show={})", target, show);
            workspace.select(dockables.get(target));
            NotificationManagerF.getInstance()
                    .notify("Demo proof loaded: " + location, Kind.INFO);
            if (System.getProperty("key.fx.verify.sequent") != null) {
                String report = sequentView.verifyPositionMapping();
                LOGGER.info("Sequent position mapping verification: {}", report);
                NotificationManagerF.getInstance()
                        .notify("Position mapping verification: " + report,
                            report.endsWith("PASS") ? Kind.INFO : Kind.ERROR);
                statusRight.setText(report);
                String hlReport = sequentView.verifySyntaxHighlighting();
                LOGGER.info("Sequent syntax highlighting verification: {}", hlReport);
                NotificationManagerF.getInstance()
                        .notify("Syntax highlighting verification: " + hlReport,
                            hlReport.endsWith("PASS") ? Kind.INFO : Kind.ERROR);
            }
            if (System.getProperty("key.fx.verify.sequentsearch") != null
                    && System.getProperty("key.fx.demo.autoprove.live") == null) {
                // without the live auto mode the sequent at load is final; with the live mode
                // the sequent search verification runs at its stop
                runSequentSearchVerification();
            }
            if (System.getProperty("key.fx.verify.tree") != null) {
                String report = proofTreeView.verifyTreeStructure();
                LOGGER.info("Proof tree structure verification: {}", report);
                NotificationManagerF.getInstance()
                        .notify("Tree structure verification: " + report,
                            report.endsWith("PASS") ? Kind.INFO : Kind.ERROR);
            }
            if (System.getProperty("key.fx.verify.search") != null
                    && System.getProperty("key.fx.demo.autoprove.live") == null) {
                // without the live auto mode the proof state at load is final (fresh or already
                // auto-closed); with the live mode the search verification runs at its stop
                runSearchVerification();
            }
            if (System.getProperty("key.fx.verify.goallist") != null) {
                LOGGER.info("Goal list verification: {}", goalListView.verifyGoalList());
            }
            if (System.getProperty("key.fx.demo.autoprove.live") != null) {
                startLiveAutoMode(env);
            }
        });
        loadTask.setOnFailed(event -> {
            Throwable error = loadTask.getException();
            LOGGER.error("Demo proof loading failed", error);
            NotificationManagerF.getInstance()
                    .notify("Demo proof loading failed: " + error.getMessage(), Kind.ERROR);
        });
        Thread loader = new Thread(loadTask, "fx-demo-proof-loader");
        loader.setDaemon(true);
        loader.start();
    }

    /**
     * Milestone M2 verification affordance: runs the automatic prover <b>after</b> the proof was
     * bound to the selection model ({@code key.fx.demo.autoprove.live}). During the run the
     * parallel prover suspends the proof's non-essential tree listeners ({@code
     * Proof#suspendNonEssentialListeners}), so no per-application events reach the views; the
     * final state is delivered via {@code autoModeStopped} — the same contract the Swing UI
     * implements ({@code MainWindow.autoModeStopped}). The structure self test afterwards proves
     * the rebuilt tree matches the final proof state. {@code key.fx.demo.maxsteps} optionally
     * limits the strategy steps (tests the non-closed case).
     */
    private void startLiveAutoMode(KeYEnvironment<DefaultUserInterfaceControl> env) {
        Proof proof = env.getLoadedProof();
        String maxSteps = System.getProperty("key.fx.demo.maxsteps");
        if (maxSteps != null && !maxSteps.isBlank()) {
            proof.getSettings().getStrategySettings()
                    .setMaxSteps(Integer.parseInt(maxSteps.trim()));
        }
        env.getProofControl().addAutoModeListener(new AutoModeListener() {
            @Override
            public void autoModeStarted(ProofEvent e) {
                LOGGER.info("Demo: live auto mode started");
            }

            @Override
            public void autoModeStopped(ProofEvent e) {
                // the parallel prover suspends the non-essential tree listeners for the whole
                // run, so the final tree state arrives only here (Swing parity:
                // MainWindow.autoModeStopped refreshes the views from the final state)
                FxUtil.runLater(() -> {
                    refreshViewsFromFinalState();
                    if (System.getProperty("key.fx.verify.search") != null) {
                        runSearchVerification();
                    }
                    if (System.getProperty("key.fx.verify.sequentsearch") != null) {
                        runSequentSearchVerification();
                    }
                    if (System.getProperty("key.fx.verify.treefilters") != null) {
                        String report = proofTreeView.verifyTreeFilters();
                        LOGGER.info("Proof tree filter verification: {}", report);
                        NotificationManagerF.getInstance()
                                .notify("Tree filter verification: " + report,
                                    report.endsWith("PASS") ? Kind.INFO : Kind.ERROR);
                    }
                    String report = proofTreeView.verifyTreeStructure() + " "
                        + proofTreeView.getLiveUpdateReport();
                    LOGGER.info("Proof tree live update verification: {}", report);
                    NotificationManagerF.getInstance()
                            .notify("Live update verification: " + report,
                                report.endsWith("PASS") ? Kind.INFO : Kind.ERROR);
                });
            }
        });
        Thread worker = new Thread(() -> {
            LOGGER.info("Demo: starting live auto mode on the selected proof");
            env.getProofControl().startAndWaitForAutoMode(proof);
            LOGGER.info("Demo: live auto mode finished");
        }, "fx-demo-live-autoprover");
        worker.setDaemon(true);
        worker.start();
    }

    /**
     * Runs the sequent search self test with the query given as the value of
     * {@code key.fx.verify.sequentsearch} (default {@code agatha}, which occurs in the Agatha
     * demo's sequent).
     */
    private void runSequentSearchVerification() {
        String query = System.getProperty("key.fx.verify.sequentsearch");
        String report = sequentView
                .verifySequentSearch(query == null || query.isBlank() ? "agatha" : query.trim());
        LOGGER.info("Sequent search verification: {}", report);
        NotificationManagerF.getInstance()
                .notify("Sequent search verification: " + report,
                    report.endsWith("PASS") ? Kind.INFO : Kind.ERROR);
    }

    /**
     * Runs the proof tree search self test with the query given as the value of
     * {@code key.fx.verify.search} (default {@code andleft}, which matches the Agatha demo's
     * rule applications).
     */
    private void runSearchVerification() {
        String query = System.getProperty("key.fx.verify.search");
        String report = proofTreeView
                .verifySearch(query == null || query.isBlank() ? "andleft" : query.trim());
        LOGGER.info("Proof tree search verification: {}", report);
        NotificationManagerF.getInstance()
                .notify("Tree search verification: " + report,
                    report.endsWith("PASS") ? Kind.INFO : Kind.ERROR);
    }

    /**
     * Refreshes all views from the final proof state. Called at auto mode stop (Swing parity:
     * {@code MainWindow.autoModeStopped}): the proof suspends its non-essential listeners during
     * the run, so no selection or structural event fires at the stop and the views would
     * otherwise show stale content.
     */
    private void refreshViewsFromFinalState() {
        Proof proof = selectionModel.getSelectedProof();
        proofTreeView.refresh();
        goalListView.setProof(proof);
        infoView.display(proof);
        sequentView.display(selectionModel.getSelectedNode());
        updateProofStatus();
    }

    /**
     * The global action keys of the Swing {@code AutoModeAction}: {@code Ctrl+Space} starts the
     * automatic prover on the selected proof, {@code Escape} stops a running one. The scene
     * handler sees the key events that no focused control consumed — an open search bar consumes
     * {@code Escape} itself (Swing parity: the Swing search bars behave the same against the
     * global stop shortcut).
     */
    private void handleMainWindowKeyPressed(KeyEvent event) {
        if (event.getCode() == KeyCode.SPACE && event.isControlDown()) {
            mediator.startAutoMode();
            event.consume();
        } else if (event.getCode() == KeyCode.ESCAPE) {
            mediator.stopAutoMode();
            event.consume();
        }
    }

    /**
     * The UI's own auto mode listener: refreshes the views from the final state after an
     * <em>interactive</em> auto mode run (Swing {@code MainWindow.autoModeStopped}). The demo's
     * live run has its own listener which also runs the verification reports; the UI listener
     * skips the refresh in that case to avoid the duplicate work.
     */
    private final AutoModeListener autoModeUiListener = new AutoModeListener() {
        @Override
        public void autoModeStarted(ProofEvent e) {
            LOGGER.info("Auto mode started");
        }

        @Override
        public void autoModeStopped(ProofEvent e) {
            if (System.getProperty("key.fx.demo.autoprove.live") != null) {
                return; // the demo listener handles the final state incl. the verification reports
            }
            FxUtil.runLater(() -> {
                refreshViewsFromFinalState();
                LOGGER.info("Views refreshed after the auto mode stop");
            });
        }
    };

    private void setWindowIcons() {
        Image icon = new Image(MainWindowF.class.getResourceAsStream(IMAGE_DIR
            + "key-color-icon-square.png"));
        if (!icon.isError()) {
            stage.getIcons().add(icon);
        }
    }

    // ------------------------------------------------------------------
    // dockables & default layout
    // ------------------------------------------------------------------

    private void buildDockables() {
        registerDockable(ID_LOADED_PROOFS, "Loaded Proofs"); // TaskTree
        dockables.put(ID_GOAL_LIST,
            new SimpleDockable(ID_GOAL_LIST, "Goal List", goalListView));
        dockables.put(ID_PROOF_TREE,
            new SimpleDockable(ID_PROOF_TREE, "Proof Tree", proofTreeView));
        dockables.put(ID_INFO_VIEW, new SimpleDockable(ID_INFO_VIEW, "Info", infoView));
        dockables.put(ID_STRATEGY,
            new SimpleDockable(ID_STRATEGY, "Strategy", strategyView));
        dockables.put(ID_SEQUENT, new SimpleDockable(ID_SEQUENT, "Sequent", sequentView));
        registerDockable(ID_SOURCE_VIEW, "Source");
    }

    private void registerDockable(String id, String title) {
        dockables.put(id,
            new SimpleDockable(id, title, placeholderContent(title)));
    }

    private List<DockWorkspace.Default> defaultLayout() {
        return List.of(new DockWorkspace.Default(DockLocation.LEFT,
            requireDockable(ID_LOADED_PROOFS)),
            new DockWorkspace.Default(DockLocation.LEFT, requireDockable(ID_GOAL_LIST)),
            new DockWorkspace.Default(DockLocation.LEFT, requireDockable(ID_PROOF_TREE)),
            new DockWorkspace.Default(DockLocation.LEFT, requireDockable(ID_INFO_VIEW)),
            new DockWorkspace.Default(DockLocation.LEFT, requireDockable(ID_STRATEGY)),
            new DockWorkspace.Default(DockLocation.MAIN, requireDockable(ID_SEQUENT)),
            new DockWorkspace.Default(DockLocation.RIGHT, requireDockable(ID_SOURCE_VIEW)));
    }

    private void restoreLayout() {
        try {
            workspace.restoreLayout(layoutStore, id -> Optional.ofNullable(dockables.get(id)));
        } catch (IOException e) {
            LOGGER.warn("Could not restore docking layout: {}", e.getMessage());
            workspace.restoreFactoryDefault();
        }
    }

    private Node placeholderContent(String title) {
        VBox box = new VBox(8);
        box.setAlignment(Pos.CENTER);
        Label heading = new Label(title);
        heading.getStyleClass().add("view-title");
        Label hint = new Label("Placeholder — the view arrives in milestone M2.");
        hint.getStyleClass().add("view-hint");
        box.getChildren().addAll(heading, hint);
        return box;
    }

    private Dockable requireDockable(String id) {
        return dockables.get(id);
    }

    // ------------------------------------------------------------------
    // menu bar, toolbars
    // ------------------------------------------------------------------

    private VBox buildTop() {
        VBox top = new VBox();
        MenuBar menuBar = buildMenuBar();
        HBox toolBarArea = new HBox(buildFileToolBar(), buildProofToolBar());
        toolBarArea.getStyleClass().add("key-toolbar-area");
        top.getChildren().addAll(menuBar, toolBarArea);
        return top;
    }

    private MenuBar buildMenuBar() {
        MenuBar menuBar = new MenuBar();
        menuBar.getMenus().addAll(buildFileMenu(), buildViewMenu(), buildProofMenu(),
            buildOptionsMenu(), buildAboutMenu());
        return menuBar;
    }

    private Menu buildFileMenu() {
        Menu file = new Menu("File");
        file.getItems().addAll(
            menuItem("Open Example…", IconFactoryF.Key.OPEN_KEY_FILE, this::notYetImplemented),
            menuItem("Open File…", "de.uka.ilkd.key.gui.actions.OpenFileAction",
                IconFactoryF.Key.OPEN_KEY_FILE, this::notYetImplemented),
            menuItem("Open Most Recent…", "de.uka.ilkd.key.gui.actions.OpenMostRecentFileAction",
                this::notYetImplemented),
            new SeparatorMenuItem(),
            menuItem("Save File…", "de.uka.ilkd.key.gui.actions.SaveFileAction",
                IconFactoryF.Key.SAVE_FILE, this::notYetImplemented),
            menuItem("Save Bundle…", "de.uka.ilkd.key.gui.actions.SaveBundleAction",
                this::notYetImplemented),
            menuItem("Quick Save", "de.uka.ilkd.key.gui.actions.QuickSaveAction",
                this::notYetImplemented),
            menuItem("Quick Load", "de.uka.ilkd.key.gui.actions.QuickLoadAction",
                this::notYetImplemented),
            new SeparatorMenuItem(),
            menuItem("Exit", "de.uka.ilkd.key.gui.actions.ExitMainAction",
                IconFactoryF.Key.QUIT, Platform::exit));
        return file;
    }

    private Menu buildViewMenu() {
        Menu view = new Menu("View");
        // placeholder toggles; wired to the real views in M2
        CheckMenuItem prettyPrint = new CheckMenuItem("Pretty Print");
        CheckMenuItem unicode = new CheckMenuItem("Unicode Symbols");
        CheckMenuItem syntaxHighlighting = new CheckMenuItem("Syntax Highlighting");
        syntaxHighlighting.setSelected(sequentView.isSyntaxHighlightingEnabled());
        syntaxHighlighting.setOnAction(
            e -> sequentView.setSyntaxHighlightingEnabled(syntaxHighlighting.isSelected()));

        ToggleGroup themeGroup = new ToggleGroup();
        RadioMenuItem lightTheme = new RadioMenuItem("Light Theme");
        RadioMenuItem darkTheme = new RadioMenuItem("Dark Theme");
        lightTheme.setToggleGroup(themeGroup);
        darkTheme.setToggleGroup(themeGroup);
        (ThemeManager.getInstance().getTheme() == Theme.DARK ? darkTheme : lightTheme)
                .setSelected(true);
        lightTheme.setOnAction(e -> setTheme(Theme.LIGHT));
        darkTheme.setOnAction(e -> setTheme(Theme.DARK));

        Menu themeMenu = new Menu("Theme");
        themeMenu.getItems().addAll(lightTheme, darkTheme);

        Menu fontSize = new Menu("Font Size");
        fontSize.getItems().addAll(
            menuItem("Increase", "de.uka.ilkd.key.gui.actions.IncreaseFontSizeAction",
                IconFactoryF.Key.PLUS, () -> changeFontSize(1)),
            menuItem("Decrease", "de.uka.ilkd.key.gui.actions.DecreaseFontSizeAction",
                IconFactoryF.Key.MINUS, () -> changeFontSize(-1)));

        view.getItems().addAll(prettyPrint, unicode, syntaxHighlighting, new SeparatorMenuItem(),
            themeMenu, fontSize);
        return view;
    }

    private Menu buildProofMenu() {
        Menu proof = new Menu("Proof");
        Menu automation = new Menu("Automation");
        MenuItem startAuto =
            menuItem("Start Automatic Proof", "de.uka.ilkd.key.gui.actions.AutoModeAction",
                IconFactoryF.Key.AUTO_MODE_START, mediator::startAutoMode);
        startAuto.disableProperty().bind(mediator.autoModeRunningProperty());
        MenuItem stopAuto = menuItem("Stop Automatic Proof", IconFactoryF.Key.AUTO_MODE_STOP,
            mediator::stopAutoMode);
        stopAuto.disableProperty().bind(mediator.autoModeRunningProperty().not());
        automation.getItems().addAll(startAuto, stopAuto);
        proof.getItems().addAll(automation, new SeparatorMenuItem(),
            menuItem("Goal Back", "de.uka.ilkd.key.gui.actions.GoalBackAction",
                IconFactoryF.Key.GOAL_BACK, this::notYetImplemented),
            menuItem("Prune Proof", "de.uka.ilkd.key.gui.actions.PruneProofAction",
                IconFactoryF.Key.PRUNE, this::notYetImplemented));
        return proof;
    }

    private Menu buildOptionsMenu() {
        Menu options = new Menu("Options");
        options.getItems().addAll(
            menuItem("Preferences…",
                "de.uka.ilkd.key.gui.settings.SettingsManager$ShowSettingsAction",
                IconFactoryF.Key.CONFIGURE, this::openSettings),
            new SeparatorMenuItem(),
            menuItem("Reset Dock Layout", this::resetLayout),
            menuItem("SMT Solvers…", IconFactoryF.Key.TOOLBOX, this::notYetImplemented));
        return options;
    }

    private Menu buildAboutMenu() {
        Menu about = new Menu("About");
        about.getItems().addAll(
            menuItem("License…", IconFactoryF.Key.INFO_VIEW, this::showLicense),
            menuItem("About KeY…", this::showAbout));
        return about;
    }

    private ToolBar buildFileToolBar() {
        ToolBar bar = new ToolBar();
        bar.getStyleClass().add("key-file-tool-bar");
        bar.getItems().addAll(
            toolbarButton("Open File", IconFactoryF.Key.OPEN_KEY_FILE, this::notYetImplemented),
            toolbarButton("Open Most Recent", IconFactoryF.Key.OPEN_MOST_RECENT,
                this::notYetImplemented),
            toolbarButton("Save File", IconFactoryF.Key.SAVE_FILE, this::notYetImplemented));
        return bar;
    }

    private ToolBar buildProofToolBar() {
        javafx.scene.control.Button startAuto =
            toolbarButton("Start Automatic Proof (Ctrl+Space)", IconFactoryF.Key.AUTO_MODE_START,
                mediator::startAutoMode);
        startAuto.disableProperty().bind(mediator.autoModeRunningProperty());
        javafx.scene.control.Button stopAuto =
            toolbarButton("Stop Automatic Proof (Escape)", IconFactoryF.Key.AUTO_MODE_STOP,
                mediator::stopAutoMode);
        stopAuto.disableProperty().bind(mediator.autoModeRunningProperty().not());
        ToolBar bar = new ToolBar();
        bar.getStyleClass().add("key-proof-tool-bar");
        bar.getItems().addAll(startAuto, stopAuto,
            toolbarButton("Goal Back", IconFactoryF.Key.GOAL_BACK, this::notYetImplemented),
            toolbarButton("Prune Proof", IconFactoryF.Key.PRUNE, this::notYetImplemented));
        return bar;
    }

    private javafx.scene.control.Button toolbarButton(String tooltip, IconFactoryF.Key icon,
            Runnable action) {
        javafx.scene.control.Button button =
            new javafx.scene.control.Button(null, IconFactoryF.createIcon(icon));
        button.setTooltip(new Tooltip(tooltip));
        button.setOnAction(e -> action.run());
        return button;
    }

    private MenuItem menuItem(String text, Runnable action) {
        return menuItem(text, null, null, action);
    }

    private MenuItem menuItem(String text, IconFactoryF.Key icon, Runnable action) {
        return menuItem(text, null, icon, action);
    }

    private MenuItem menuItem(String text, String actionId, Runnable action) {
        return menuItem(text, actionId, null, action);
    }

    /**
     * Creates a menu item with an optional icon and accelerator (bound via the
     * {@link KeyStrokeManagerF}).
     */
    private MenuItem menuItem(String text, String actionId, IconFactoryF.Key icon,
            Runnable action) {
        MenuItem item = new MenuItem(text);
        if (icon != null) {
            item.setGraphic(IconFactoryF.createIcon(icon));
        }
        if (actionId != null) {
            KeyStrokeManagerF.getInstance().binding(actionId).ifPresent(item::setAccelerator);
        }
        item.setOnAction(e -> action.run());
        return item;
    }

    // ------------------------------------------------------------------
    // status bar & actions
    // ------------------------------------------------------------------

    private HBox buildStatusBar() {
        HBox bar = new HBox();
        bar.getStyleClass().add("status-bar");
        bar.setPadding(new Insets(2, 8, 2, 8));
        statusLeft.setAlignment(Pos.CENTER_LEFT);
        statusLeft.setMaxWidth(Double.MAX_VALUE);
        HBox.setHgrow(statusLeft, Priority.ALWAYS);
        Region spacer = new Region();
        HBox.setHgrow(spacer, Priority.ALWAYS);
        statusRight.setAlignment(Pos.CENTER_RIGHT);
        bar.getChildren().addAll(statusLeft, spacer, statusRight);
        return bar;
    }

    private void updateStatus() {
        Theme theme = ThemeManager.getInstance().getTheme();
        int sizeIndex = ConfigF.DEFAULT.sizeIndex();
        updateProofStatus();
        statusRight.setText("Theme: " + theme.name().toLowerCase() + " · Font size: "
            + ConfigF.SIZES[sizeIndex]);
    }

    /**
     * Sets the left status text from the current selection: the copyright if no proof is
     * selected, otherwise the proof name plus its closed state or open-goal count.
     */
    private void updateProofStatus() {
        if (!FxUtil.isFxThread()) {
            FxUtil.runLater(this::updateProofStatus);
            return;
        }
        Proof proof = selectionModel.getSelectedProof();
        if (proof == null) {
            statusLeft.setText(KeYConstants.COPYRIGHT);
            return;
        }
        if (proof.closed()) {
            statusLeft.setText("Proof: " + proof.name() + " (closed)");
        } else {
            statusLeft.setText("Proof: " + proof.name() + " · " + proof.openGoals().size()
                + " open goal(s)");
        }
    }

    private void setTheme(Theme theme) {
        ThemeManager.getInstance().setTheme(theme);
    }

    private void changeFontSize(int delta) {
        ViewSettings viewSettings = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        int next = Math.clamp(viewSettings.sizeIndex() + delta, 0, ConfigF.SIZES.length - 1);
        viewSettings.setFontIndex(next);
        NotificationManagerF.getInstance()
                .notify("Font size " + ConfigF.SIZES[next] + " (will apply to the views in M2).");
    }

    private void openSettings() {
        SettingsManagerF.getInstance().openSettings(stage);
    }

    private void resetLayout() {
        workspace.restoreFactoryDefault();
    }

    private void showLicense() {
        NotificationManagerF.getInstance().notify(
            KeYConstants.COPYRIGHT + " KeY is free software and comes with ABSOLUTELY NO "
                + "WARRANTY. See About | License.",
            Kind.INFO);
    }

    private void showAbout() {
        NotificationManagerF.getInstance().notify(
            KeYResourceManager.getManager().getUserInterfaceTitle() + " — JavaFX UI (key.ui.fx).");
    }

    private void notYetImplemented() {
        NotificationManagerF.getInstance().notify(
            "This action arrives in a later milestone of the key.ui.fx rewrite.", Kind.WARNING);
    }

    private void registerSettingsProviders() {
        SettingsManagerF.getInstance().addProvider(new ThemeSettingsProviderF());
    }
}
