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
import java.util.Properties;
import java.util.function.Consumer;
import javafx.application.Platform;
import javafx.beans.property.ReadOnlyBooleanWrapper;
import javafx.concurrent.Task;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.control.Alert;
import javafx.scene.control.CheckBox;
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
import de.uka.ilkd.key.gui.fx.actions.QuickSaveF;
import de.uka.ilkd.key.gui.fx.configuration.ConfigF;
import de.uka.ilkd.key.gui.fx.docking.DockLayoutStore;
import de.uka.ilkd.key.gui.fx.docking.DockLocation;
import de.uka.ilkd.key.gui.fx.docking.DockWorkspace;
import de.uka.ilkd.key.gui.fx.docking.Dockable;
import de.uka.ilkd.key.gui.fx.docking.DockingLayoutF;
import de.uka.ilkd.key.gui.fx.docking.SimpleDockable;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF;
import de.uka.ilkd.key.gui.fx.goallist.GoalListViewF;
import de.uka.ilkd.key.gui.fx.infoview.InfoViewF;
import de.uka.ilkd.key.gui.fx.join.JoinMergeVerifyF;
import de.uka.ilkd.key.gui.fx.keyshortcuts.KeyStrokeManagerF;
import de.uka.ilkd.key.gui.fx.mergerule.MergeRuleCompletionF;
import de.uka.ilkd.key.gui.fx.nodeviews.SequentViewF;
import de.uka.ilkd.key.gui.fx.notification.NotificationCenterF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF.Kind;
import de.uka.ilkd.key.gui.fx.proofdiff.ProofDiffFrameF;
import de.uka.ilkd.key.gui.fx.proofmanagement.ProofManagementDialogF;
import de.uka.ilkd.key.gui.fx.proofmanagement.ProofManagerF;
import de.uka.ilkd.key.gui.fx.prooftree.ProofTreeViewF;
import de.uka.ilkd.key.gui.fx.recentfiles.RecentFilesF;
import de.uka.ilkd.key.gui.fx.settings.SettingsManagerF;
import de.uka.ilkd.key.gui.fx.sourceview.SourceViewF;
import de.uka.ilkd.key.gui.fx.strategy.StrategySelectionViewF;
import de.uka.ilkd.key.gui.fx.tacletmatch.TacletMatchVerifyF;
import de.uka.ilkd.key.gui.fx.tasktree.TaskTreeF;
import de.uka.ilkd.key.gui.fx.theme.Theme;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.io.GZipProofSaver;
import de.uka.ilkd.key.proof.io.ProofBundleSaver;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.io.SingleThreadProblemLoader;
import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;
import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.KeYResourceManager;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.util.javafx.FxUtil;

import org.jspecify.annotations.Nullable;
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

    // docking: layout slots, maximize toggle, shutdown persistence and self test (Swing
    // DockingLayout)
    private final DockingLayoutF dockingLayout;

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
     * seam: the window-side {@link de.uka.ilkd.key.control.UserInterfaceControl} (Swing
     * {@code MainWindow.getUserInterface()} returning the {@code WindowUserInterfaceControl}):
     * routes the core's status/task/exception/warning callbacks into this window and hosts the
     * interactive rule-completion registry. Created once for the whole application lifetime
     * (like the Swing original).
     */
    private final WindowUserInterfaceControlF userInterface =
        new WindowUserInterfaceControlF(this);

    {
        // joinmerge: register the interactive merge-rule completion with the seam registry
        // (Swing parity: MergeRuleCompletion.INSTANCE is registered in the
        // WindowUserInterfaceControl constructor, WindowUserInterfaceControl.java:81);
        // the join trigger JoinActionF.run(...) is wired with the future sequent-view
        // context menu (Swing JoinMenuItem, CurrentGoalViewMenu.java:235-238)
        userInterface.register(MergeRuleCompletionF.INSTANCE);
    }

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
     * proofmgmt: the multi-proof state (the Swing {@code TaskTreeModel} state of the
     * {@code TaskTree}): the loaded proofs and the active one, consulted by the Loaded Proofs
     * view and the Proof Management dialog.
     */
    private final ProofManagerF proofManager = new ProofManagerF();

    /**
     * proofmgmt: the "Loaded Proofs" view (JavaFX port of the Swing {@code TaskTree}): lists the
     * loaded proofs with status and open-goal count and switches the active proof on click.
     */
    private final TaskTreeF loadedProofs = new TaskTreeF(proofManager);

    /**
     * proofmgmt: the environment of the most recent load; the Proof Management dialog (Swing
     * {@code ProofManagementDialog}, opened from the File menu) operates on its init config and
     * starts proofs via its user interface control.
     */
    private @Nullable KeYEnvironment<DefaultUserInterfaceControl> lastEnvironment;

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
        // docking: the layout extension needs the workspace and the layout store
        this.dockingLayout = new DockingLayoutF(this);
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
        // docking: Ctrl+M maximize toggle (bibliothek CControl.KEY_MAXIMIZE_CHANGE) and the
        // shutdown persistence of the Swing GUIListener.shutDown
        dockingLayout.install(scene);
        stage.setScene(scene);
        stage.show();

        restoreLayout();

        ThemeManager.getInstance().themeProperty().addListener((obs, old, theme) -> updateStatus());
        updateStatus();

        wireSequentView();
        recentFiles.setOnChange(this::updateRecentFilesMenu);
        recentFiles.load();
        startDemoProofLoad();
        // proofmgmt: the Loaded Proofs view's clicks and the Proof Management dialog route the
        // active-proof switch through the selection model (the Swing mediator path)
        proofManager.setActivationHandler(this::activateProof);
        // proofmgmt: self test hook (independent of the demo load; the verification loads its
        // own examples so that it also runs without key.fx.demo.sequent)
        if (System.getProperty("key.fx.verify.proofmgmt") != null) {
            runProofMgmtVerification();
        }

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
     * @return the docking layout store (docking: needed by the {@link DockingLayoutF} slots)
     */
    public DockLayoutStore getLayoutStore() {
        return layoutStore;
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

    /**
     * seam: the window's {@link de.uka.ilkd.key.control.UserInterfaceControl} (Swing
     * {@code MainWindow.getUserInterface()}); the host of the status/task/exception callbacks
     * and the rule-completion registry (merge point for the interactive completion ports).
     */
    public WindowUserInterfaceControlF getUserInterfaceControl() {
        return userInterface;
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
        loadedProofs.attach(selectionModel); // proofmgmt: row highlight follows the active proof
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
     * #reloadLastFile()}, the recent-files menu, quick load). The optional {@code
     * key.fx.demo.autoprove} run happens inside the load task, so only demo loads prove
     * automatically.
     * <p>
     * Note: recent files are registered by the <em>callers</em> — the menu actions register the
     * file before starting the load; the demo load must not pollute the user's shared
     * {@code recentFiles_v2.json}.
     *
     * @param location the problem, proof or Java file to load
     * @param demo whether this is the demo property load (notification prefix "Demo proof")
     */
    private void startProofLoad(Path location, boolean demo) {
        startProofLoad(location, demo, null);
    }

    /**
     * Loads a proof or problem file, optionally a specific proof out of a proof bundle.
     *
     * @param location the problem, proof, Java file or proof bundle to load
     * @param demo whether this is the demo property load (notification prefix "Demo proof")
     * @param proofFilename the proof to load relative to the bundle root, or {@code null} if
     *        {@code location} is not a proof bundle
     */
    private void startProofLoad(Path location, boolean demo, @Nullable Path proofFilename) {
        // pure .key problems carry no Java source; the source view then shows the problem file.
        // Proof bundles carry their own sources (or none) — never show the bundle zip as text
        if (proofFilename == null) {
            sourceView.setFallbackSourceFile(location);
        }
        Task<KeYEnvironment<DefaultUserInterfaceControl>> loadTask = new Task<>() {
            @Override
            protected KeYEnvironment<DefaultUserInterfaceControl> call() throws Exception {
                KeYEnvironment<DefaultUserInterfaceControl> env;
                if (proofFilename != null) {
                    // proof bundle: load the user-chosen proof from the bundle (Swing
                    // ProblemLoader.setProofPath in loadProofFromBundle). The core loader unzips
                    // the bundle to a temporary directory and loads the selected proof file from
                    // there. This mirrors KeYEnvironment.load, which offers no proofFilename
                    // parameter.
                    // seam: load through the window's own UserInterfaceControlF instead of the
                    // headless DefaultUserInterfaceControl, so its callbacks reach the UI
                    var ui = getUserInterfaceControl();
                    var loader = new SingleThreadProblemLoader(location, null, null, null, null,
                        false, ui, false, new Properties());
                    loader.setProofFilename(proofFilename);
                    loader.load();
                    env = new KeYEnvironment<>(ui, loader.getInitConfig(), loader.getProof(),
                        loader.getProofScript(), loader.getResult());
                } else {
                    // seam: load through the window's own UserInterfaceControlF instead of the
                    // headless KeYEnvironment.load (Swing parity: KeYEnvironment.loadInMainWindow
                    // uses the WindowUserInterfaceControl as UI, WindowUserInterfaceControl.java
                    // :600-613), so status/task/exception callbacks reach the UI
                    var ui = getUserInterfaceControl();
                    var loader = new SingleThreadProblemLoader(location, null, null, null, null,
                        false, ui, false, new Properties());
                    loader.load();
                    env = new KeYEnvironment<>(ui, loader.getInitConfig(), loader.getProof(),
                        loader.getProofScript(), loader.getResult());
                }
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
            // notification: register the notification framework's auto-mode tracker on the
            // proof control (Swing parity: the NotificationManager constructor registers its
            // listener, NotificationManager.java:99-101; created in MainWindow.java:333)
            env.getProofControl().addAutoModeListener(
                NotificationCenterF.getInstance().notificationListener());
            // route the proof through the selection model: setSelectedProof invokes the
            // mediator's setProof (listener swap, abbreviation rebind, OSS refresh) and then
            // selects the first open goal or a leaf, which the views observe.
            selectionModel.setSelectedProof(env.getLoadedProof());
            // proofmgmt: register the loaded proof in the multi-proof state (the Loaded Proofs
            // view follows) and remember the environment for the Proof Management dialog
            lastEnvironment = env;
            proofManager.addProof(env.getLoadedProof());
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
            if (System.getProperty("key.fx.verify.sequentsearchmodes") != null
                    && System.getProperty("key.fx.demo.autoprove.live") == null) {
                // ditto; runs after the plain search verification and restores the plain view
                runSequentSearchModesVerification();
            }
            if (System.getProperty("key.fx.verify.updatehighlight") != null) {
                runUpdateHighlightVerification();
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
            // joinmerge: run the join/merge dialog self test (key.fx.verify.joinmerge)
            if (System.getProperty("key.fx.verify.joinmerge") != null) {
                runJoinMergeVerification(env);
            }
            if (System.getProperty("key.fx.verify.proofdiff") != null) {
                String report = ProofDiffFrameF.verifyDiffLogic();
                LOGGER.info("Proof diff verification: {}", report);
                NotificationManagerF.getInstance()
                        .notify("Proof diff verification: " + report,
                            report.endsWith("PASS") ? Kind.INFO : Kind.ERROR);
            }
            if (System.getProperty("key.fx.verify.notifications") != null) {
                // notification: notification-framework self test (fires each notification type
                // and asserts the actions' visible counterparts; report logged/toasted there)
                NotificationCenterF.getInstance()
                        .verifyNotifications(selectionModel.getSelectedProof());
            }
            if (System.getProperty("key.fx.verify.docking") != null) { // docking: docking self test
                String report = dockingLayout.runSelfTest();
                LOGGER.info("Docking self test: {}", report);
                NotificationManagerF.getInstance()
                        .notify("Docking self test: " + report,
                            report.startsWith("PASS") ? Kind.INFO : Kind.ERROR);
            }
            // seam: key.fx.verify.uicontrol — self test of the WindowUserInterfaceControlF seam
            // (status line, IssueDialogF, LogViewF, AutoDismissDialogF) after the demo load
            if (System.getProperty("key.fx.verify.uicontrol") != null) {
                UiControlSelfTestF.run(this);
            }
            // tacletmatch: run the interactive taclet application self test (dialog render,
            // cancel keeps the proof, apply adds to the proof) after the demo load
            if (System.getProperty("key.fx.verify.tacletmatch") != null) {
                TacletMatchVerifyF.runTacletMatchVerification(env.getLoadedProof(),
                    env.getProofControl(), stage, mediator.getNotationInfo());
            }
            if (System.getProperty("key.fx.demo.autoprove.live") != null) {
                startLiveAutoMode(env);
            }
        });
        loadTask.setOnFailed(event -> {
            Throwable error = loadTask.getException();
            // notification: TODO-merge wire into WindowUserInterfaceControlF — the seam agent
            // routes exceptions through NotificationCenterF.handleNotificationEvent(
            // new ExceptionFailureEventF(...)) there (Swing parity:
            // IssueDialog.showExceptionDialog)
            LOGGER.error((demo ? "Demo proof" : "Proof") + " loading failed", error);
            // seam: loading errors surface in the IssueDialog (Swing parity: the
            // ProblemLoader branch of WindowUserInterfaceControl.taskFinishedInternal,
            // WindowUserInterfaceControl.java:236-244, calls IssueDialog.showExceptionDialog;
            // the FX load task throws instead of reporting a failed TaskFinishedInfo)
            IssueDialogF.showExceptionDialog(getStage(), error);
            NotificationManagerF.getInstance()
                    .notify((demo ? "Demo proof" : "Proof") + " loading failed: "
                        + error.getMessage(), Kind.ERROR);
        });
        Thread loader = new Thread(loadTask, "fx-demo-proof-loader");
        loader.setDaemon(true);
        loader.start();
    }

    // ------------------------------------------------------------------
    // file menu actions: open / reload / recent files / save (M3/M4)
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
     * {@code WindowUserInterfaceControl.loadProblem} registers before the load starts).
     * <p>
     * Proof bundles ({@code .zproof}, Swing {@code OpenFileAction} special case) first show the
     * {@link ProofSelectionDialogF}; the chosen proof is loaded from the bundle and the
     * <em>bundle</em> is registered in the recent files (Swing
     * {@code WindowUserInterfaceControl.loadProofFromBundle}). A bare {@code .java} file shows
     * the load-behaviour warning (Swing {@code OpenFileAction}, view setting
     * {@code notifyLoadBehaviour}).
     *
     * @param file the file to load
     */
    public void openProofFile(Path file) {
        // special case proof bundles -> allow to select the proof to load
        if (ProofSelectionDialogF.isProofBundle(file)) {
            Path proofPath = ProofSelectionDialogF.chooseProofToLoad(file, stage);
            if (proofPath == null) {
                return; // canceled by user!
            }
            recentFiles.add(file.toAbsolutePath().toString(), null, false, null);
            startProofLoad(file, false, proofPath);
            return;
        }

        warnOnBareJavaFile(file);
        recentFiles.add(file.toAbsolutePath().toString(), null, false, null);
        startProofLoad(file, false);
    }

    /**
     * The load-behaviour warning for bare Java files (Swing
     * {@code OpenFileAction.actionPerformed}):
     * shown when the view setting {@code notifyLoadBehaviour} is active, with a "don't show this
     * warning again" checkbox writing the setting back (persisted via
     * {@code ProofIndependentSettings.saveSettings}).
     *
     * @param file the file about to be loaded
     */
    private void warnOnBareJavaFile(Path file) {
        ViewSettings viewSettings = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        if (!viewSettings.getNotifyLoadBehaviour() || !file.toString().endsWith(".java")) {
            return;
        }
        CheckBox checkbox = new CheckBox("Don't show this warning again");
        VBox message = new VBox(6,
            new Label("When you load a Java file, all java files in the current"),
            new Label("directory and all subdirectories will be loaded as well."), checkbox);
        Alert alert = new Alert(Alert.AlertType.WARNING);
        alert.setTitle("Please note");
        alert.setHeaderText(null);
        alert.getDialogPane().setContent(message);
        alert.initOwner(stage);
        ExampleChooserF.themeDialogPane(alert);
        alert.showAndWait();
        viewSettings.setNotifyLoadBehaviour(!checkbox.isSelected());
        ProofIndependentSettings.DEFAULT_INSTANCE.saveSettings();
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
        // Swing KeYFileChooser offers the COMPRESSED_FILTER ("compressed proof files
        // (.proof.gz)") alongside the default filter
        chooser.getExtensionFilters().add(new FileChooser.ExtensionFilter(
            "KeY proof files (*.proof)", "*.proof"));
        chooser.getExtensionFilters().add(new FileChooser.ExtensionFilter(
            "compressed proof files (.proof.gz)", "*.proof.gz"));
        File file = chooser.showSaveDialog(stage);
        if (file == null) {
            return;
        }
        if (file.getParentFile() != null) {
            lastSelectedDir = file.getParentFile().toPath();
        }
        Path target = file.toPath().toAbsolutePath();
        // compression by file name: Swing KeYFileChooser.useCompression() checks the selected
        // file name for the ".proof.gz" extension and uses the GZipProofSaver in that case
        // (there is no separate checkbox in the current Swing save dialog)
        ProofSaver saver;
        if (target.getFileName().toString().endsWith(".proof.gz")) {
            saver = new GZipProofSaver(proof, target.toString(), KeYConstants.INTERNAL_VERSION);
        } else {
            saver = new ProofSaver(proof, target, KeYConstants.INTERNAL_VERSION);
        }
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
     * The Open Example action (Swing {@code OpenExampleAction}): shows the example chooser
     * (Swing {@code ExampleChooser.showInstance(Main.getExamplesDir())}; the directory comes from
     * the {@code key.examples.dir} property set by the run task) and loads the chosen file like
     * any other problem file.
     * <p>
     * Swing registers the example in the recent files through {@code loadProblem} — the port
     * does the same via {@link #openProofFile(Path)}.
     */
    private void openExampleChooser() {
        Path file = ExampleChooserF.showInstance(null, stage);
        if (file != null) {
            openProofFile(file);
        }
    }

    /**
     * The Save Bundle action (Swing {@code SaveBundleAction} +
     * {@code WindowUserInterfaceControl.saveProofBundle}): a save dialog with the bundle filter
     * and the sanitized proof name + ".zproof", then the core {@link ProofBundleSaver} (which
     * packs the proof and all dependencies into a zip archive via the proof's FileRepo) on the
     * FX thread (the Swing original runs on the EDT as well).
     */
    private void saveProofBundle() {
        Proof proof = selectionModel.getSelectedProof();
        if (proof == null) {
            return; // the action is disabled without a proof (Swing updateStatus)
        }
        FileChooser chooser = new FileChooser();
        chooser.setTitle("Choose filename to save proof");
        if (lastSelectedDir != null && Files.isDirectory(lastSelectedDir)) {
            chooser.setInitialDirectory(lastSelectedDir.toFile());
        }
        // Swing KeYFileChooser.PROOF_BUNDLE_FILTER
        chooser.getExtensionFilters()
                .add(new FileChooser.ExtensionFilter("proof bundles (.zproof)", "*.zproof"));
        chooser.setInitialFileName(initialSaveFileName(proof, ".zproof"));
        File file = chooser.showSaveDialog(stage);
        if (file == null) {
            return;
        }
        if (file.getParentFile() != null) {
            lastSelectedDir = file.getParentFile().toPath();
        }
        Path target = file.toPath().toAbsolutePath();
        ProofBundleSaver saver = new ProofBundleSaver(proof, target);
        try {
            String errorMsg = saver.save();
            if (errorMsg != null) {
                LOGGER.error("Saving proof bundle failed: {}", errorMsg);
                NotificationManagerF.getInstance()
                        .notify("Saving Proof failed. Error: " + errorMsg, Kind.ERROR);
            } else {
                proof.setProofFile(target);
                LOGGER.info("Proof bundle saved to {}", target);
                NotificationManagerF.getInstance()
                        .notify("Proof bundle saved to " + target, Kind.INFO);
            }
        } catch (Exception e) {
            LOGGER.error("Saving proof bundle failed", e);
            NotificationManagerF.getInstance()
                    .notify("Saving Proof failed. Error: " + e.getMessage(), Kind.ERROR);
        }
    }

    /**
     * The Quick Save action (Swing {@code QuickSaveAction}, F5): saves the selected proof to the
     * temporary quick save location ({@link QuickSaveF#QUICK_SAVE_PATH}).
     */
    private void quickSave() {
        QuickSaveF.quickSave(this);
    }

    /**
     * The Quick Load action (Swing {@code QuickLoadAction}, F6): loads the quick save location.
     */
    private void quickLoad() {
        QuickSaveF.quickLoad(this);
    }

    /**
     * Shows a warning toast (the JavaFX counter-part of Swing {@code MainWindow.popupWarning},
     * which opens a modal message dialog; the JavaFX UI reports via toasts).
     *
     * @param message the warning message
     */
    public void popupWarning(String message) {
        NotificationManagerF.getInstance().notify(message, Kind.WARNING);
    }

    /**
     * Sets the left status line text (Swing {@code MainWindow.setStatusLine}).
     *
     * @param status the status message
     */
    public void setStatusLine(String status) {
        statusLeft.setText(status);
    }

    /**
     * seam: resets the status line to the proof summary (Swing
     * {@code MainWindow.setStandardStatusLine}); called by
     * {@link #userInterface} on {@code resetStatus}.
     */
    public void resetStatusLine() {
        updateProofStatus();
    }

    /**
     * seam: current left status text (used by the {@code key.fx.verify.uicontrol} self test).
     */
    public String getStatusLineText() {
        return statusLeft.getText();
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
                    if (System.getProperty("key.fx.verify.sequentsearchmodes") != null) {
                        runSequentSearchModesVerification();
                    }
                    if (System.getProperty("key.fx.verify.updatehighlight") != null) {
                        runUpdateHighlightVerification();
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
     * Runs the search mode self test (Highlight/Hide/Regroup) with the query given as the value
     * of {@code key.fx.verify.sequentsearchmodes} (like the other search verifications the VALUE
     * is the query itself; the flag value {@code 1} falls back to the
     * {@code key.fx.verify.sequentsearch} query, default {@code agatha}); restores the plain
     * view.
     */
    private void runSequentSearchModesVerification() {
        String value = System.getProperty("key.fx.verify.sequentsearchmodes");
        String query;
        if (value == null || value.isBlank() || "1".equals(value.trim())) {
            String searchQuery = System.getProperty("key.fx.verify.sequentsearch");
            query = searchQuery == null || searchQuery.isBlank() ? "agatha" : searchQuery.trim();
        } else {
            query = value.trim();
        }
        String report = sequentView.verifySearchModes(query);
        LOGGER.info("Sequent search modes verification: {}", report);
        NotificationManagerF.getInstance()
                .notify("Sequent search modes verification: " + report,
                    report.endsWith("PASS") ? Kind.INFO : Kind.ERROR);
    }

    /**
     * Runs the update-highlight overlay self test (needs a sequent that prints update operators,
     * e.g. the normalisation11.key demo).
     */
    private void runUpdateHighlightVerification() {
        String report = sequentView.verifyUpdateHighlights();
        LOGGER.info("Update highlight verification: {}", report);
        NotificationManagerF.getInstance()
                .notify("Update highlight verification: " + report,
                    report.endsWith("PASS") ? Kind.INFO : Kind.ERROR);
    }

    /**
     * Runs the join/merge dialog self test ({@code key.fx.verify.joinmerge}); the dialogs are
     * constructed directly with the loaded proof, see {@link JoinMergeVerifyF}.
     *
     * @param env the environment of the loaded proof
     */
    // joinmerge: TODO-merge registration seam — once the FX rule-application completion registry
    // exists (WindowUserInterfaceControlF, port of Swing WindowUserInterfaceControl.java:74-82),
    // register the interactive completions there via
    // uiControl.register(MergeRuleCompletionF.INSTANCE);
    // the join trigger is JoinActionF.run(partners, proof, proofControl, owner) for the future
    // sequent-view context menu (Swing JoinMenuItem via CurrentGoalViewMenu.java:235-238).
    // joinmerge: keep this hook minimal, all logic lives in JoinMergeVerifyF
    private void runJoinMergeVerification(KeYEnvironment<DefaultUserInterfaceControl> env) {
        JoinMergeVerifyF.run(stage, env.getLoadedProof(), env.getProofControl());
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
        // notification: proof-closed + "Automated proof search" notifications after an automatic
        // run (Swing parity: KeYMediator.proofClosed fires a ProofClosedNotificationEvent;
        // WindowUserInterfaceControl.taskFinishedInternal fires the showNotification
        // information, gated by ViewSettings.notificationAfterMacro)
        NotificationCenterF.getInstance().afterAutoModeFinished(proof, stage.isFocused());
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
                // notification: the proof-closed / "Automated proof search" notifications are
                // fired inside refreshViewsFromFinalState (the framework's only auto-mode-stop
                // hook, covering the interactive and the demo-live run)
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
        // proofmgmt: the Loaded Proofs view replaces the M1 placeholder dockable (JavaFX port of
        // the Swing TaskTree)
        dockables.put(ID_LOADED_PROOFS,
            new SimpleDockable(ID_LOADED_PROOFS, "Loaded Proofs", loadedProofs));
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
        MenuItem openExample =
            menuItem("Open Example…", "de.uka.ilkd.key.gui.actions.OpenExampleAction",
                IconFactoryF.Key.OPEN_KEY_FILE, this::openExampleChooser);
        // Swing disables all actions during auto mode (like the Open File action)
        openExample.disableProperty().bind(mediator.autoModeRunningProperty());
        MenuItem saveBundle =
            menuItem("Save Bundle…", "de.uka.ilkd.key.gui.actions.SaveBundleAction",
                this::saveProofBundle);
        // Swing SaveBundleAction: enabled only when a proof is selected (updateStatus); disabled
        // during auto mode like all interaction
        saveBundle.disableProperty()
                .bind(mediator.autoModeRunningProperty().or(proofLoaded.not()));
        MenuItem quickSave =
            menuItem("Quick Save", "de.uka.ilkd.key.gui.actions.QuickSaveAction", this::quickSave);
        // Swing QuickSaveAction: enableWhenProofLoaded; disabled during auto mode
        quickSave.disableProperty()
                .bind(mediator.autoModeRunningProperty().or(proofLoaded.not()));
        MenuItem quickLoad =
            menuItem("Quick Load", "de.uka.ilkd.key.gui.actions.QuickLoadAction", this::quickLoad);
        // Swing QuickLoadAction has no proof enablement — it always tries to load the quick save
        // location (a missing file fails the load); disabled during auto mode like all interaction
        quickLoad.disableProperty().bind(mediator.autoModeRunningProperty());
        // proofmgmt: Swing ProofManagementAction (menu + toolbar button): opens the Proof
        // Management dialog for the most recently loaded problem's init config
        MenuItem proofManagement =
            menuItem("Proof Management…", "de.uka.ilkd.key.gui.actions.ProofManagementAction",
                IconFactoryF.Key.PROOF_MANAGEMENT, this::openProofManagement);
        proofManagement.disableProperty().bind(mediator.autoModeRunningProperty());
        file.getItems().addAll(
            openExample,
            openFile,
            reload,
            new SeparatorMenuItem(),
            proofManagement,
            saveFile,
            saveBundle,
            quickSave,
            quickLoad,
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
            themeMenu, fontSize, new SeparatorMenuItem(),
            menuItem("Visual Node Diff", "de.uka.ilkd.key.gui.proofdiff.ProofDiffFrame$Action",
                this::showProofDiffFrame),
            new SeparatorMenuItem(),
            // docking: named layout slots (Swing DockingLayout, menu path View > Layout)
            dockingLayout.layoutMenu(),
            // seam: the Swing LogView is opened by a status-line extension button
            // (ShowLogAction; no FX extension SPI yet), so the FX entry point is a View menu
            // item (LogViewF.showInstance)
            menuItem("Log View", "de.uka.ilkd.key.gui.actions.LogViewAction",
                this::showLogView));
        return view;
    }

    /**
     * seam: opens the log view window (Swing {@code ShowLogAction} →
     * {@code LogView.showInstance}, {@code LogView.java:88-126}).
     */
    private void showLogView() {
        LogViewF.showInstance(getStage());
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
        // proofmgmt: Swing file toolbar has the Proof Management button as well
        javafx.scene.control.Button proofManagement =
            toolbarButton("Proof Management", IconFactoryF.Key.PROOF_MANAGEMENT,
                this::openProofManagement);
        proofManagement.disableProperty().bind(mediator.autoModeRunningProperty());
        bar.getItems().addAll(openFile, reload, saveFile, proofManagement);
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
     * {@link KeyStrokeManagerF}). The item is registered with the manager, so a shortcut change
     * in the settings dialog updates the accelerator live.
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
            manager.register(item, actionId);
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

    /**
     * Opens the visual node diff window (Swing {@code ProofDiffFrame.Action}: a new window per
     * invocation, non-modal, always enabled).
     */
    private void showProofDiffFrame() {
        new ProofDiffFrameF(this).showCenteredOnOwner();
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

    // ------------------------------------------------------------------
    // proof management (proofmgmt: JavaFX port of the Swing ProofManagementDialog
    // and the Loaded Proofs/TaskTree view)
    // ------------------------------------------------------------------

    /**
     * proofmgmt: opens the Proof Management dialog for the most recently loaded problem's init
     * config (Swing {@code ProofManagementAction}); proofs started or selected in the dialog are
     * registered in the multi-proof state and activated via {@link #activateProof(Proof)}.
     */
    private void openProofManagement() {
        if (lastEnvironment == null) {
            popupWarning("No problem has been loaded yet. Load a Java source or a "
                + "problem with contracts first.");
            return;
        }
        ProofManagementDialogF.showInstance(stage, lastEnvironment.getInitConfig(),
            lastEnvironment.getUi(), this::activateAndRegisterProof,
            selectionModel.getSelectedProof());
    }

    /**
     * proofmgmt: activates the given proof (the selection model routes the switch through the
     * mediator, which swaps the proof listeners and refreshes the views).
     *
     * @param proof the proof to make the active one
     */
    private void activateProof(Proof proof) {
        selectionModel.setSelectedProof(proof);
    }

    /**
     * proofmgmt: the proof selector handed to the Proof Management dialog: a proof started in
     * the dialog is registered in the multi-proof state (it appears in the Loaded Proofs view)
     * and activated.
     *
     * @param proof the started or selected proof
     */
    private void activateAndRegisterProof(Proof proof) {
        proofManager.addProof(proof);
        activateProof(proof);
    }

    /**
     * proofmgmt: the {@code key.fx.verify.proofmgmt} self test driver. The value selects what is
     * verified: {@code 1} (default) the Proof Management dialog with a real JML example,
     * {@code 2} the Loaded Proofs view with two loaded proofs and active-proof switching,
     * {@code all} both.
     */
    private void runProofMgmtVerification() {
        String mode = System.getProperty("key.fx.verify.proofmgmt", "1").trim();
        if (mode.equals("2")) {
            runLoadedProofsVerification();
        } else {
            runProofMgmtDialogVerification();
            if (mode.equals("all")) {
                runLoadedProofsVerification();
            }
        }
    }

    /**
     * proofmgmt: loads an example with the core {@link KeYEnvironment} on a background thread
     * and hands it to the given continuation on the FX thread. The examples of this self test
     * are loaded independently of the demo load and do not touch the recent files.
     */
    private void loadProofMgmtExample(Path location,
            Consumer<KeYEnvironment<DefaultUserInterfaceControl>> onSuccess) {
        Task<KeYEnvironment<DefaultUserInterfaceControl>> task = new Task<>() {
            @Override
            protected KeYEnvironment<DefaultUserInterfaceControl> call() throws Exception {
                return KeYEnvironment.load(location);
            }
        };
        task.setOnSucceeded(e -> onSuccess.accept(task.getValue()));
        task.setOnFailed(e -> {
            LOGGER.error("Proof management self test: loading {} failed", location,
                task.getException());
            NotificationManagerF.getInstance()
                    .notify("Proof management self test load failed: " + location, Kind.ERROR);
        });
        Thread worker = new Thread(task, "fx-proofmgmt-loader");
        worker.setDaemon(true);
        worker.start();
    }

    /**
     * proofmgmt: path of an example file, relative to the examples directory of the run task
     * ({@code key.examples.dir}); absolute paths pass through.
     */
    private static Path proofMgmtExample(String relative) {
        Path path = Path.of(relative);
        if (path.isAbsolute()) {
            return path;
        }
        return Path.of(System.getProperty("key.examples.dir", "key.ui/examples"), relative);
    }

    /**
     * proofmgmt: the Proof Management dialog self test ({@code key.fx.verify.proofmgmt=1}). The
     * dialog is exercised with a real JML example (default
     * {@code heap/vstte10_01_SumAndMax/SumAndMax_sumAndMax.key}, override with
     * {@code key.fx.demo.proofmgmt}): the dialog is shown non-blocking first (the structural
     * checks read the laid-out scene graph), then the programmatic interactions run and are
     * reported to the log; the dialog stays open for the visual inspection (the run continues
     * when the dialog is closed with Cancel).
     */
    private void runProofMgmtDialogVerification() {
        String example = System.getProperty("key.fx.demo.proofmgmt",
            "heap/vstte10_01_SumAndMax/SumAndMax_sumAndMax.key");
        loadProofMgmtExample(proofMgmtExample(example), env -> {
            // the dialog self test's problem becomes the "most recent" one, so the dialog can
            // also be opened from the File menu afterwards
            lastEnvironment = env;
            ProofManagementDialogF dialog = ProofManagementDialogF
                    .createForVerification(stage, env.getInitConfig(), env.getUi(),
                        this::activateAndRegisterProof);
            // showForVerification first (non-blocking stage.show()), then the structural self
            // test (ProofManagementDialogF.verifyDialog requires the shown dialog)
            dialog.showForVerification();
            String report = dialog.verifyDialog();
            LOGGER.info("Proof management dialog verification: {}", report);
            NotificationManagerF.getInstance()
                    .notify("Proof management dialog verification: " + report,
                        report.endsWith("PASS") ? Kind.INFO : Kind.ERROR);
            // the dialog stays open for the visual inspection; the user closes it with Cancel
        });
    }

    /**
     * proofmgmt: the Loaded Proofs view self test ({@code key.fx.verify.proofmgmt=2}, also part
     * of {@code all}). Loads two examples (default Agatha and the useQuery problem, override
     * with {@code key.fx.demo.sequent2} and {@code key.fx.demo.sequent3}), registers both in the
     * {@link ProofManagerF} and switches the active proof back and forth (the Swing TaskTree
     * click semantics), verifying the rows, the selection sync and that the sequent view follows
     * the switch.
     */
    private void runLoadedProofsVerification() {
        String first = System.getProperty("key.fx.demo.sequent2",
            "firstTouch/01-Agatha/project.key");
        String second = System.getProperty("key.fx.demo.sequent3",
            "standard_key/queries/useQuery.key");
        loadProofMgmtExample(proofMgmtExample(first), envA -> loadProofMgmtExample(
            proofMgmtExample(second), envB -> {
                Proof proofA = envA.getLoadedProof();
                Proof proofB = envB.getLoadedProof();
                proofManager.addProof(proofA);
                proofManager.addProof(proofB);
                // A1: both proofs are registered (the Loaded Proofs view binds to the manager)
                check("both proofs registered in ProofManagerF",
                    proofManager.contains(proofA) && proofManager.contains(proofB));
                // A2: the Loaded Proofs view lists both with name/status/open-goal rows
                check("Loaded Proofs view lists both proofs",
                    loadedProofs.getProofCount() == 2);
                String rows = loadedProofs.verifyContent();
                LOGGER.info("Loaded proofs rows verification: {}", rows);
                check("Loaded Proofs rows in sync (" + rows + ")", rows.endsWith("PASS"));
                // switch the active proof: B, then back to A (Swing TaskTree problemChosen)
                proofManager.setActive(proofB);
                check("switch to " + proofB.name() + ": selection model follows",
                    selectionModel.getSelectedProof() == proofB);
                check("switch to " + proofB.name() + ": sequent view follows",
                    sequentView.getProof() == proofB);
                check("switch to " + proofB.name() + ": rows follow",
                    loadedProofs.verifyContent().endsWith("PASS"));
                proofManager.setActive(proofA);
                check("switch back to " + proofA.name() + ": selection model follows",
                    selectionModel.getSelectedProof() == proofA);
                check("switch back to " + proofA.name() + ": sequent view follows",
                    sequentView.getProof() == proofA);
                check("switch back to " + proofA.name() + ": rows follow",
                    loadedProofs.verifyContent().endsWith("PASS"));
                boolean ok = proofManager.getActiveProof() == proofA
                        && selectionModel.getSelectedProof() == proofA;
                LOGGER.info("Loaded proofs verification: {}", ok ? "PASS" : "FAIL");
                NotificationManagerF.getInstance()
                        .notify("Loaded proofs verification: " + (ok ? "PASS" : "FAIL"),
                            ok ? Kind.INFO : Kind.ERROR);
            }));
    }

    /**
     * proofmgmt: logs one PASS/FAIL self-test assertion line (the {@code
     * key.fx.verify.proofmgmt} report).
     *
     * @param what the assertion description
     * @param ok whether the assertion holds
     */
    private void check(String what, boolean ok) {
        LOGGER.info("proofmgmt self test: {} {}", what, ok ? "PASS" : "FAIL");
    }
}
