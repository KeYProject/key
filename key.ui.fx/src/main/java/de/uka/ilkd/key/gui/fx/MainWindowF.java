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
import de.uka.ilkd.key.core.fx.KeYSelectionModel;
import de.uka.ilkd.key.gui.fx.configuration.ConfigF;
import de.uka.ilkd.key.gui.fx.docking.DockLayoutStore;
import de.uka.ilkd.key.gui.fx.docking.DockLocation;
import de.uka.ilkd.key.gui.fx.docking.DockWorkspace;
import de.uka.ilkd.key.gui.fx.docking.Dockable;
import de.uka.ilkd.key.gui.fx.docking.SimpleDockable;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF;
import de.uka.ilkd.key.gui.fx.infoview.InfoViewF;
import de.uka.ilkd.key.gui.fx.keyshortcuts.KeyStrokeManagerF;
import de.uka.ilkd.key.gui.fx.nodeviews.SequentViewF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF.Kind;
import de.uka.ilkd.key.gui.fx.prooftree.ProofTreeViewF;
import de.uka.ilkd.key.gui.fx.settings.SettingsManagerF;
import de.uka.ilkd.key.gui.fx.settings.ThemeSettingsProviderF;
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
            // the mediator observes the proof control (auto mode state, closed-goal counter)
            mediator.attach(env.getProofControl());
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
            statusLeft.setText("Proof: " + env.getLoadedProof().name());
            if (System.getProperty("key.fx.verify.sequent") != null) {
                String report = sequentView.verifyPositionMapping();
                LOGGER.info("Sequent position mapping verification: {}", report);
                NotificationManagerF.getInstance()
                        .notify("Position mapping verification: " + report,
                            report.endsWith("PASS") ? Kind.INFO : Kind.ERROR);
                statusRight.setText(report);
            }
            if (System.getProperty("key.fx.verify.tree") != null) {
                String report = proofTreeView.verifyTreeStructure();
                LOGGER.info("Proof tree structure verification: {}", report);
                NotificationManagerF.getInstance()
                        .notify("Tree structure verification: " + report,
                            report.endsWith("PASS") ? Kind.INFO : Kind.ERROR);
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
                    proofTreeView.refresh();
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
        registerDockable(ID_GOAL_LIST, "Goal List");
        dockables.put(ID_PROOF_TREE,
            new SimpleDockable(ID_PROOF_TREE, "Proof Tree", proofTreeView));
        dockables.put(ID_INFO_VIEW, new SimpleDockable(ID_INFO_VIEW, "Info", infoView));
        registerDockable(ID_STRATEGY, "Strategy");
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
        automation.getItems().addAll(
            menuItem("Start Automatic Proof", "de.uka.ilkd.key.gui.actions.AutoModeAction",
                IconFactoryF.Key.AUTO_MODE_START, this::notYetImplemented),
            menuItem("Stop Automatic Proof", IconFactoryF.Key.AUTO_MODE_STOP,
                this::notYetImplemented));
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
        ToolBar bar = new ToolBar();
        bar.getStyleClass().add("key-proof-tool-bar");
        bar.getItems().addAll(
            toolbarButton("Start Automatic Proof", IconFactoryF.Key.AUTO_MODE_START,
                this::notYetImplemented),
            toolbarButton("Stop Automatic Proof", IconFactoryF.Key.AUTO_MODE_STOP,
                this::notYetImplemented),
            toolbarButton("Goal Back", IconFactoryF.Key.GOAL_BACK, this::notYetImplemented),
            toolbarButton("Prune Proof", IconFactoryF.Key.PRUNE, this::notYetImplemented));
        return bar;
    }

    private Node toolbarButton(String tooltip, IconFactoryF.Key icon, Runnable action) {
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
        statusLeft.setText(KeYConstants.COPYRIGHT);
        statusRight.setText("Theme: " + theme.name().toLowerCase() + " · Font size: "
            + ConfigF.SIZES[sizeIndex]);
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
