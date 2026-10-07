/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import javafx.application.Platform;
import javafx.beans.property.ReadOnlyBooleanWrapper;
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
import javafx.scene.control.OverrunStyle;
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
import javafx.stage.FileChooser;
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
import de.uka.ilkd.key.gui.fx.recentfiles.RecentFilesF;
import de.uka.ilkd.key.gui.fx.settings.SettingsManagerF;
import de.uka.ilkd.key.gui.fx.sourceview.SourceViewF;
import de.uka.ilkd.key.gui.fx.strategy.StrategySelectionViewF;
import de.uka.ilkd.key.gui.fx.theme.Theme;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;
import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.KeYResourceManager;
import de.uka.ilkd.key.util.MiscTools;

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
     * The source view (first M2 version): shows the Java source file(s) relevant to the selected
     * proof (via {@code ProofJavaSourceCollection} + {@code FileRepo}, like the Swing view);
     * pure {@code .key} problems without Java source show the loaded problem file as a fallback.
     */
    private final SourceViewF sourceView = new SourceViewF();

    /**
     * The recent files store: the same {@code recentFiles_v2.json} as the Swing UI, so both UIs
     * share one list. Populated by the File menu actions only — the demo property load must not
     * pollute the user's shared recent-files file.
     */
    private final RecentFilesF recentFiles = new RecentFilesF();

    /**
     * The "Recent Files" submenu of the File menu; rebuilt by {@link #updateRecentFilesMenu()}
     * whenever the store changes.
     */
    private final Menu recentFilesMenu = new Menu("Recent Files");

    /**
     * Last directory of the open/save dialogs (Swing {@code OpenFileAction.lastSelectedPath}).
     */
    private Path lastSelectedDir = Path.of(System.getProperty("user.dir"));

    /**
     * Whether a proof is selected (updated in {@link #updateProofStatus()}); the enablement
     * condition of the save action (Swing {@code enableWhenProofLoaded}).
     */
    private final ReadOnlyBooleanWrapper proofLoaded =
        new ReadOnlyBooleanWrapper(this, "proofLoaded");

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
        recentFiles.setOnChange(this::updateRecentFilesMenu);
        recentFiles.load();
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
     * @return the mediator of the window (Swing {@code MainWindow.getMediator()})
     */
    public KeYMediatorF getMediator() {
        return mediator;
    }

    /**
     * @return the primary stage of the main window (owner for dialogs)
     */
    public Stage getStage() {
        return stage;
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
        sourceView.attach(selectionModel);
        // the hook doubles as the :99 verification signal (same line as the standalone driver)
        sourceView.setOnContentLoaded(
            () -> LOGGER.info("Source self test: {}", sourceView.verifySourceView()));
        selectionModel.addKeYSelectionListenerChecked(statusSelectionListener);
        sequentView.setOnPosSelected(pos -> {
            if (pos == null) {
                statusRight.setText("");
                return;
            }
            String text = sequentView.getHighlightedText(pos);
            // the status bar stays single-line: flatten the pretty-printed term and cap it; the
            // full position is in the log line below
            String flat = text.replaceAll("\\s+", " ").strip();
            if (flat.length() > 120) {
                flat = flat.substring(0, 117) + "...";
            }
            statusRight.setText(flat.isBlank() ? String.valueOf(pos) : flat);
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
        startProofLoad(Path.of(file), true);
    }

    /**
     * Loads a proof or problem file with the core {@link KeYEnvironment} on a background thread
     * and routes the loaded proof through the mediator/selection model. Shared by the demo
     * property load and the File menu actions ({@link #openFileChooser()}, {@link
     * #reloadLastFile()}, the recent-files menu). The optional {@code key.fx.demo.autoprove}
     * run happens inside the load task, so only demo loads prove automatically.
     * <p>
     * Note: recent files are registered by the <em>callers</em> — the menu actions register the
     * file before starting the load; the demo load must not pollute the user's shared
     * {@code recentFiles_v2.json}.
     *
     * @param location the problem, proof or Java file to load
     * @param demo whether this is the demo property load (notification prefix "Demo proof")
     */
    private void startProofLoad(Path location, boolean demo) {
        // pure .key problems carry no Java source; the source view then shows the problem file
        sourceView.setFallbackSourceFile(location);
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
            LOGGER.info("Selecting dockable '{}' (key.fx.show={})", target, show);
            workspace.select(dockables.get(target));
            NotificationManagerF.getInstance()
                    .notify((demo ? "Demo proof loaded: " : "Proof loaded: ") + location,
                        Kind.INFO);
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
            LOGGER.error((demo ? "Demo proof" : "Proof") + " loading failed", error);
            NotificationManagerF.getInstance()
                    .notify((demo ? "Demo proof" : "Proof") + " loading failed: "
                        + error.getMessage(), Kind.ERROR);
        });
        Thread loader = new Thread(loadTask, "fx-demo-proof-loader");
        loader.setDaemon(true);
        loader.start();
    }

    // ------------------------------------------------------------------
    // file menu actions: open / reload / recent files / save (M3)
    // ------------------------------------------------------------------

    /**
     * The Open File action (Swing {@code OpenFileAction}): a file chooser for problem, proof and
     * Java files, remembering the last directory like the Swing original.
     */
    private void openFileChooser() {
        FileChooser chooser = new FileChooser();
        chooser.setTitle("Select file to load proof or problem");
        if (lastSelectedDir != null && Files.isDirectory(lastSelectedDir)) {
            chooser.setInitialDirectory(lastSelectedDir.toFile());
        }
        // Swing KeYFileChooser.DEFAULT_FILTER
        chooser.getExtensionFilters().add(new FileChooser.ExtensionFilter(
            "Java files, (compressed) KeY files, proof bundles, and source directories",
            "*.java", "*.key", "*.proof", "*.proof.gz", "*.zproof"));
        chooser.getExtensionFilters()
                .add(new FileChooser.ExtensionFilter("All Files", "*.*"));
        File file = chooser.showOpenDialog(stage);
        if (file == null) {
            return;
        }
        if (file.getParentFile() != null) {
            lastSelectedDir = file.getParentFile().toPath();
        }
        openProofFile(file.toPath());
    }

    /**
     * Loads the given file and registers it in the recent files list (Swing
     * {@code WindowUserInterfaceControl.loadProblem} registers before the load starts). Proof
     * bundles require the Swing {@code ProofSelectionDialog} flow and are deferred.
     *
     * @param file the file to load
     */
    private void openProofFile(Path file) {
        if (file.toString().endsWith(".zproof")) {
            LOGGER.info("Proof bundle requested: {} (deferred)", file);
            NotificationManagerF.getInstance()
                    .notify("Proof bundles (.zproof) are not supported yet.", Kind.WARNING);
            return;
        }
        recentFiles.add(file.toAbsolutePath().toString(), null, false, null);
        startProofLoad(file, false);
    }

    /**
     * The Reload action (Swing {@code OpenMostRecentFileAction}): loads the most recent file.
     */
    private void reloadLastFile() {
        String recent = recentFiles.getMostRecent();
        if (recent == null) {
            // the item is disabled without a proof/recent; keep the Swing action's silent guard
            LOGGER.info("Reload requested, but no recent file exists");
            return;
        }
        openProofFile(Path.of(recent));
    }

    /**
     * The Save File action (Swing {@code SaveFileAction} +
     * {@code WindowUserInterfaceControl.saveProof}): a save dialog pre-filled with the proof's
     * file (or a sanitized proof name), then {@link ProofSaver} on the FX thread (the Swing
     * original runs on the EDT as well; the interaction lock prevents concurrent auto mode).
     */
    private void saveProofFile() {
        Proof proof = selectionModel.getSelectedProof();
        if (proof == null) {
            return; // the action is disabled without a proof (Swing enableWhenProofLoaded)
        }
        if (mediator.isInAutoMode()) {
            // Swing wraps the save in stopInterface/startInterface: no interaction while saving
            LOGGER.info("Save requested during auto mode");
            NotificationManagerF.getInstance()
                    .notify("Cannot save while the automatic prover is running.", Kind.WARNING);
            return;
        }
        FileChooser chooser = new FileChooser();
        chooser.setTitle("Choose filename to save proof");
        if (lastSelectedDir != null && Files.isDirectory(lastSelectedDir)) {
            chooser.setInitialDirectory(lastSelectedDir.toFile());
        }
        chooser.setInitialFileName(initialSaveFileName(proof, ".proof"));
        File file = chooser.showSaveDialog(stage);
        if (file == null) {
            return;
        }
        if (file.getParentFile() != null) {
            lastSelectedDir = file.getParentFile().toPath();
        }
        Path target = file.toPath().toAbsolutePath();
        // the Swing chooser offers a "compressed" checkbox (GZipProofSaver); deferred, the plain
        // saver is the default
        ProofSaver saver = new ProofSaver(proof, target, KeYConstants.INTERNAL_VERSION);
        try {
            String errorMsg = saver.save();
            if (errorMsg != null) {
                LOGGER.error("Saving proof failed: {}", errorMsg);
                NotificationManagerF.getInstance()
                        .notify("Saving proof failed. Error: " + errorMsg, Kind.ERROR);
            } else {
                proof.setProofFile(target);
                LOGGER.info("Proof saved to {}", target);
                NotificationManagerF.getInstance()
                        .notify("Proof saved to " + target, Kind.INFO);
            }
        } catch (Exception e) {
            LOGGER.error("Saving proof failed", e);
            NotificationManagerF.getInstance()
                    .notify("Saving proof failed. Error: " + e.getMessage(), Kind.ERROR);
        }
    }

    /**
     * The initial file name of the save dialog (Swing {@code WindowUserInterfaceControl.fileName}):
     * the file the proof was loaded from if it already is a {@code .proof} file, otherwise the
     * sanitized proof name.
     */
    private static String initialSaveFileName(Proof proof, String extension) {
        Path proofFile = proof.getProofFile();
        if (proofFile != null && proofFile.toString().endsWith(extension)
                && proofFile.getFileName() != null) {
            return proofFile.getFileName().toString();
        }
        String name = proof.name().toString();
        for (String suffix : List.of(".key", ".proof")) {
            if (name.endsWith(suffix)) {
                name = name.substring(0, name.length() - suffix.length());
                break;
            }
        }
        return MiscTools.toValidFileName(name) + extension;
    }

    /**
     * Rebuilds the Recent Files submenu from the store (invoked after every store change): the
     * entries show their short unique file names (Swing {@code ShortUniqueFileNames}) plus the
     * profile suffix for entries loaded with a non-default profile.
     */
    private void updateRecentFilesMenu() {
        if (!FxUtil.isFxThread()) {
            FxUtil.runLater(this::updateRecentFilesMenu);
            return;
        }
        List<RecentFilesF.Entry> entries = recentFiles.getEntries();
        List<String> names = RecentFilesF
                .uniqueNames(entries.stream().map(RecentFilesF.Entry::path).toList());
        recentFilesMenu.getItems().clear();
        for (int i = 0; i < entries.size(); i++) {
            RecentFilesF.Entry entry = entries.get(i);
            String name = names.get(i);
            // Swing's RecentFileAction labels entries loaded with a non-default profile
            String text = entry.profile() != null ? name + " (Profile: " + entry.profile() + ")"
                    : name;
            recentFilesMenu.getItems()
                    .add(menuItem(text, () -> openProofFile(Path.of(entry.path()))));
        }
        // an empty submenu would render as a dark clickable nothing (Swing leaves it enabled)
        recentFilesMenu.setDisable(entries.isEmpty());
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
        dockables.put(ID_SOURCE_VIEW,
            new SimpleDockable(ID_SOURCE_VIEW, "Source", buildSourceViewContent()));
    }

    /**
     * The content of the source view dockable: the source area with a one-line header showing
     * the currently displayed file (the standalone driver shows the same header).
     */
    private Node buildSourceViewContent() {
        Label header = new Label(SourceViewF.NO_SOURCE);
        header.getStyleClass().add("source-view-header");
        header.textProperty().bind(sourceView.headerTextProperty());
        header.setTextOverrun(OverrunStyle.ELLIPSIS);
        return new BorderPane(sourceView, header, null, null, null);
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
        MenuItem openFile = menuItem("Open File…", "de.uka.ilkd.key.gui.actions.OpenFileAction",
            IconFactoryF.Key.OPEN_KEY_FILE, this::openFileChooser);
        openFile.disableProperty().bind(mediator.autoModeRunningProperty());
        MenuItem reload =
            menuItem("Reload", "de.uka.ilkd.key.gui.actions.OpenMostRecentFileAction",
                this::reloadLastFile);
        // Swing OpenMostRecentFileAction: enabled when a proof is loaded (the action then reloads
        // the most recent file; disabled during auto mode like all interaction)
        reload.disableProperty()
                .bind(mediator.autoModeRunningProperty().or(proofLoaded.not()));
        MenuItem saveFile = menuItem("Save File…", "de.uka.ilkd.key.gui.actions.SaveFileAction",
            IconFactoryF.Key.SAVE_FILE, this::saveProofFile);
        // Swing SaveFileAction: enableWhenProofLoaded; interaction is locked during auto mode
        saveFile.disableProperty()
                .bind(mediator.autoModeRunningProperty().or(proofLoaded.not()));
        file.getItems().addAll(
            menuItem("Open Example…", "de.uka.ilkd.key.gui.actions.OpenExampleAction",
                IconFactoryF.Key.OPEN_KEY_FILE, this::notYetImplemented),
            openFile,
            reload,
            new SeparatorMenuItem(),
            saveFile,
            menuItem("Save Bundle…", "de.uka.ilkd.key.gui.actions.SaveBundleAction",
                this::notYetImplemented),
            menuItem("Quick Save", "de.uka.ilkd.key.gui.actions.QuickSaveAction",
                this::notYetImplemented),
            menuItem("Quick Load", "de.uka.ilkd.key.gui.actions.QuickLoadAction",
                this::notYetImplemented),
            new SeparatorMenuItem(),
            recentFilesMenu,
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
        // theme switches from elsewhere (e.g. the settings dialog) update the menu radios
        ThemeManager.getInstance().themeProperty().addListener(
            (obs, old, theme) -> (theme == Theme.DARK ? darkTheme : lightTheme).setSelected(true));

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
                IconFactoryF.Key.GOAL_BACK, mediator::goalBack),
            menuItem("Prune Proof", "de.uka.ilkd.key.gui.actions.PruneProofAction",
                IconFactoryF.Key.PRUNE, mediator::pruneProof));
        return proof;
    }

    private Menu buildOptionsMenu() {
        Menu options = new Menu("Options");
        options.getItems().addAll(
            menuItem("Settings",
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
        javafx.scene.control.Button openFile =
            toolbarButton("Browse and load problem or proof files",
                IconFactoryF.Key.OPEN_KEY_FILE, this::openFileChooser);
        openFile.disableProperty().bind(mediator.autoModeRunningProperty());
        javafx.scene.control.Button reload =
            toolbarButton("Reload last opened file", IconFactoryF.Key.OPEN_MOST_RECENT,
                this::reloadLastFile);
        reload.disableProperty()
                .bind(mediator.autoModeRunningProperty().or(proofLoaded.not()));
        javafx.scene.control.Button saveFile =
            toolbarButton("Save current proof", IconFactoryF.Key.SAVE_FILE, this::saveProofFile);
        saveFile.disableProperty()
                .bind(mediator.autoModeRunningProperty().or(proofLoaded.not()));
        bar.getItems().addAll(openFile, reload, saveFile);
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
            toolbarButton("Goal Back", IconFactoryF.Key.GOAL_BACK, mediator::goalBack),
            toolbarButton("Prune Proof", IconFactoryF.Key.PRUNE, mediator::pruneProof));
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
            KeyStrokeManagerF manager = KeyStrokeManagerF.getInstance();
            manager.binding(actionId).ifPresent(item::setAccelerator);
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
        // both labels must never drive the bar's size: a Label's min size defaults to its text
        // size, and a long (multi-line) term text would blow the bar up and squeeze the workspace
        statusLeft.setAlignment(Pos.CENTER_LEFT);
        statusLeft.setTextOverrun(OverrunStyle.ELLIPSIS);
        statusLeft.setMinWidth(0);
        statusLeft.setMinHeight(0);
        statusLeft.setMaxWidth(Double.MAX_VALUE);
        HBox.setHgrow(statusLeft, Priority.ALWAYS);
        Region spacer = new Region();
        HBox.setHgrow(spacer, Priority.ALWAYS);
        statusRight.setAlignment(Pos.CENTER_RIGHT);
        statusRight.setTextOverrun(OverrunStyle.ELLIPSIS);
        statusRight.setMinWidth(0);
        statusRight.setMinHeight(0);
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
        proofLoaded.set(proof != null);
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
        SettingsManagerF.getInstance().showSettingsDialog(this);
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
}
