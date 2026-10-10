/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Field;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Properties;
import java.util.ServiceLoader;
import java.util.function.Consumer;
import javafx.animation.KeyFrame;
import javafx.animation.Timeline;
import javafx.application.Platform;
import javafx.beans.property.ReadOnlyBooleanWrapper;
import javafx.collections.ObservableList;
import javafx.concurrent.Task;
import javafx.event.Event;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.geometry.Side;
import javafx.scene.Cursor;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.control.Alert;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.control.ButtonType;
import javafx.scene.control.CheckBox;
import javafx.scene.control.CheckMenuItem;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Control;
import javafx.scene.control.CustomMenuItem;
import javafx.scene.control.Label;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuBar;
import javafx.scene.control.MenuItem;
import javafx.scene.control.OverrunStyle;
import javafx.scene.control.RadioMenuItem;
import javafx.scene.control.SeparatorMenuItem;
import javafx.scene.control.Tab;
import javafx.scene.control.TextArea;
import javafx.scene.control.ToggleGroup;
import javafx.scene.control.ToolBar;
import javafx.scene.control.Tooltip;
import javafx.scene.image.Image;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCombination;
import javafx.scene.input.KeyEvent;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Pane;
import javafx.scene.layout.Priority;
import javafx.scene.layout.Region;
import javafx.scene.layout.StackPane;
import javafx.scene.layout.VBox;
import javafx.stage.FileChooser;
import javafx.stage.Stage;
import javafx.stage.WindowEvent;
import javafx.util.Duration;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.core.fx.KeYSelectionModel;
import de.uka.ilkd.key.gui.fx.actions.QuickSaveF;
import de.uka.ilkd.key.gui.fx.colors.ColorPaletteF;
import de.uka.ilkd.key.gui.fx.colors.ColorSettingsF;
import de.uka.ilkd.key.gui.fx.configuration.ConfigF;
import de.uka.ilkd.key.gui.fx.contractcompletions.BlockContractExternalCompletionF;
import de.uka.ilkd.key.gui.fx.contractcompletions.BlockContractInternalCompletionF;
import de.uka.ilkd.key.gui.fx.contractcompletions.DependencyContractCompletionF;
import de.uka.ilkd.key.gui.fx.contractcompletions.FunctionalOperationContractCompletionF;
import de.uka.ilkd.key.gui.fx.contractcompletions.InvariantConfiguratorF;
import de.uka.ilkd.key.gui.fx.contractcompletions.LoopInvariantRuleCompletionF;
import de.uka.ilkd.key.gui.fx.dialogs.DialogsVerifyF;
import de.uka.ilkd.key.gui.fx.dialogs.FeedbackDialogF;
import de.uka.ilkd.key.gui.fx.dialogs.LemmaSelectionDialogF;
import de.uka.ilkd.key.gui.fx.dialogs.LoadUserTacletsDialogF;
import de.uka.ilkd.key.gui.fx.dialogs.RunAllProofsF;
import de.uka.ilkd.key.gui.fx.docking.DockLayoutStore;
import de.uka.ilkd.key.gui.fx.docking.DockLocation;
import de.uka.ilkd.key.gui.fx.docking.DockWorkspace;
import de.uka.ilkd.key.gui.fx.docking.Dockable;
import de.uka.ilkd.key.gui.fx.docking.DockingLayoutF;
import de.uka.ilkd.key.gui.fx.docking.SimpleDockable;
import de.uka.ilkd.key.gui.fx.drawer.DrawerF;
import de.uka.ilkd.key.gui.fx.drawer.DrawerItemF;
import de.uka.ilkd.key.gui.fx.extension.KeYGuiExtensionFacadeF;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF;
import de.uka.ilkd.key.gui.fx.goallist.GoalListViewF;
import de.uka.ilkd.key.gui.fx.help.HelpFacadeF;
import de.uka.ilkd.key.gui.fx.infoview.InfoViewF;
import de.uka.ilkd.key.gui.fx.join.JoinMergeVerifyF;
import de.uka.ilkd.key.gui.fx.keyshortcuts.KeyStrokeManagerF;
import de.uka.ilkd.key.gui.fx.mergerule.MergeRuleCompletionF;
import de.uka.ilkd.key.gui.fx.nodeviews.SequentMenuModelF;
import de.uka.ilkd.key.gui.fx.nodeviews.SequentTermContextMenuF;
import de.uka.ilkd.key.gui.fx.nodeviews.SequentViewF;
import de.uka.ilkd.key.gui.fx.notification.NotificationCenterF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF.Kind;
import de.uka.ilkd.key.gui.fx.notification.ProofStatisticsDialogF;
import de.uka.ilkd.key.gui.fx.notification.events.ExceptionFailureEventF;
import de.uka.ilkd.key.gui.fx.originlabels.OriginLabelsF;
import de.uka.ilkd.key.gui.fx.plugins.javac.JavacSettingsProviderF;
import de.uka.ilkd.key.gui.fx.profileloading.LoadingOptionsDialogF;
import de.uka.ilkd.key.gui.fx.profileloading.LoadingOptionsDialogF.LoadOptions;
import de.uka.ilkd.key.gui.fx.profileloading.WDLoadOptionPanelF;
import de.uka.ilkd.key.gui.fx.proofdiff.ProofDiffFrameF;
import de.uka.ilkd.key.gui.fx.proofmanagement.KnownTypesDialogF;
import de.uka.ilkd.key.gui.fx.proofmanagement.ProofManagementDialogF;
import de.uka.ilkd.key.gui.fx.proofmanagement.ProofManagerF;
import de.uka.ilkd.key.gui.fx.prooftree.ProofTreeVerifyF;
import de.uka.ilkd.key.gui.fx.prooftree.ProofTreeViewF;
import de.uka.ilkd.key.gui.fx.recentfiles.RecentFilesF;
import de.uka.ilkd.key.gui.fx.settings.ActiveSettingsDialogF;
import de.uka.ilkd.key.gui.fx.settings.SettingsManagerF;
import de.uka.ilkd.key.gui.fx.settings.SettingsProviderF;
import de.uka.ilkd.key.gui.fx.settings.ToolTipOptionsDialogF;
import de.uka.ilkd.key.gui.fx.smt.SolverListenerF;
import de.uka.ilkd.key.gui.fx.soundiness.SoundinessAnalyzer;
import de.uka.ilkd.key.gui.fx.soundiness.SoundinessDialogF;
import de.uka.ilkd.key.gui.fx.sourceview.SourceViewF;
import de.uka.ilkd.key.gui.fx.strategy.StrategySelectionViewF;
import de.uka.ilkd.key.gui.fx.tacletmatch.TacletMatchVerifyF;
import de.uka.ilkd.key.gui.fx.tasktree.TaskTreeF;
import de.uka.ilkd.key.gui.fx.theme.Theme;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.macros.AutoPilotPrepareProofMacro;
import de.uka.ilkd.key.macros.DefaultAutoMacro;
import de.uka.ilkd.key.macros.FullAutoPilotProofMacro;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ScriptAwareMacro;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.DefaultProfileResolver;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.io.AutoSaver;
import de.uka.ilkd.key.proof.io.GZipProofSaver;
import de.uka.ilkd.key.proof.io.ProofBundleSaver;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.io.SingleThreadProblemLoader;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.settings.FeatureSettings;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings.ProgressMode;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SolverTypeCollection;
import de.uka.ilkd.key.taclettranslation.lemma.TacletLoader;
import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader;
import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.KeYResourceManager;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
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

    // menu: MP5 — external targets of the About menu's browser actions (Swing
    // KeYProjectHomepageAction.url / CreateGithubIssueAction.URL), opened via the
    // HelpFacadeF browser seam (host services).
    private static final String KEY_PROJECT_URL = "https://www.key-project.org/";
    private static final String GITHUB_ISSUE_URL = "https://github.com/keyproject/key/issues/new";

    // menu: MP5 — the "Run All Proofs" QA feature lives behind the same feature flag as the
    // Swing original (Swing MainWindow.FEATURE_BULK_UI_TEST, MainWindow.java:109-113). The
    // feature is already registered in the shared FeatureSettings.FEATURES registry by the
    // Swing side in a full build; the stream lookup reuses it, the createFeature fallback
    // covers a key.ui.fx-only run (otherwise the same id would register twice, which the
    // Swing FeatureSettingsPanel would then list twice).
    private static final FeatureSettings.Feature FEATURE_BULK_UI_TEST =
        FeatureSettings.Feature.FEATURES.stream().filter(f -> "BULK_UI_TEST".equals(f.id()))
                .findFirst()
                .orElseGet(() -> FeatureSettings.createFeature("BULK_UI_TEST",
                    "Activates the 'Run All Proofs' action that allows you to run multiple"
                        + " proofs inside the UI.",
                    false));

    // menu: MP5 — the batch-mode help text of the "Lemma Generation (Batch Mode)" info dialog
    // (Swing LemmaGenerationBatchModeAction.DESCRIPTION, trimmed of the trailing blank line).
    private static final String BATCH_MODE_TEXT =
        """
                In case that one wants to prove a huge set of taclets, it can be convenient and useful to do this automatically.
                The new lemma generation offers now the possibility to use the batch mode of the KeY system
                in order to generate and prove the proof obligations for the correctness of (non-axiomatic) taclets.

                The basic command using the batch mode is:

                runProver --justify-rules  FILE1 --jr-axioms FILE2 --jr-signature FILE3

                FILE1: The file containing the taclets that should be proved sound.
                FILE2: The file containing the taclets that should be used as axioms when proving the taclets of FILE1
                being sound.
                FILE3: The file containing the signature that should be used for loading the taclets.
                If this option is not set, the signature declared in FILE1 is used.

                In order to store the resulting proofs to files one can set the option "--jr-saveProofToFile true".
                The corresponding proofs are stored into the folder in which FILE1 is located. In case that one wants to
                store the proofs into another folder, one can specify the path of the folder by
                "--jr-pathOfResult PATH_OF_DEST_FOLDER".
                Some more options are available, which are shown when using the command:

                runProver --help
                in the batch mode.""";

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
        // contractcompletions (P2b): register the interactive contract/invariant completions
        // (Swing parity: WindowUserInterfaceControl constructor, WindowUserInterfaceControl
        // .java:74-82 — FunctionalOperationContractCompletion (:76),
        // DependencyContractCompletion (:77), LoopInvariantRuleCompletion (:78),
        // BlockContractInternalCompletion(mainWindow) (:79),
        // BlockContractExternalCompletion(mainWindow) (:80)); the dialogs of the completions
        // are the FX ports in de.uka.ilkd.key.gui.fx.contractcompletions
        userInterface.register(new FunctionalOperationContractCompletionF());
        userInterface.register(new DependencyContractCompletionF());
        userInterface.register(new LoopInvariantRuleCompletionF());
        userInterface.register(new BlockContractInternalCompletionF());
        userInterface.register(new BlockContractExternalCompletionF());
        // contractcompletions (P2b): the invariant configurator parses with the editor's
        // abbreviation map (Swing: MainWindow.getMediator().getNotationInfo().getAbbrevMap(),
        // InvariantConfigurator.getAbbrevMap)
        InvariantConfiguratorF.setAbbrevMap(mediator.getNotationInfo().getAbbrevMap());
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
     * menu: MP3b — the selection history backing the View menu Back / Forward actions (Swing
     * {@code MainWindow.selectionHistory}, {@code new SelectionHistory(mediator)}): traces the
     * user-selected proof nodes and exposes the Back/Forward enablement as JavaFX properties.
     */
    private final SelectionHistoryF selectionHistory = new SelectionHistoryF(selectionModel);

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
     * drawer: MP10 — the west/east/south drawer hosts of the main window (Java port of the
     * TornadoFX {@code Drawer}, package {@code de.uka.ilkd.key.gui.fx.drawer}). The panels that
     * used to live in the left/right docking areas are now toggle buttons in these drawers:
     * dragging a button onto another drawer moves the panel to that port
     * ({@link DrawerF#transferItem(DrawerItemF, DrawerF)}), dragging within a bar reorders the
     * split ({@link DrawerF#moveItem(int, int)}). The docking centre only hosts the sequent.
     */
    private DrawerF westDrawer;
    private DrawerF eastDrawer;
    private DrawerF southDrawer;

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
     * menu: MP5 — whether the {@link FeatureSettings} listener of the "Run All Proofs" menu item
     * (see {@link #FEATURE_BULK_UI_TEST} / {@link #buildProveSubmenu()}) has been registered;
     * the parity self test rebuilds the menu bar, so the registration happens at most once.
     */
    private boolean bulkUiTestListenerRegistered;

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
        buildDrawerHosts();

        BorderPane root = new BorderPane();
        root.setTop(buildTop());
        // drawer: MP10 — the workspace (the sequent) stays the centre of the main area; the
        // west/east/south drawers host the panels that previously lived in the docking areas
        BorderPane mainArea = new BorderPane();
        mainArea.setCenter(workspace.getRoot());
        mainArea.setLeft(westDrawer);
        mainArea.setRight(eastDrawer);
        mainArea.setBottom(southDrawer);
        StackPane center = new StackPane(mainArea);
        // inputfreeze (P1): the blocking overlay covers the main area (workspace + drawers) for
        // the duration of an auto mode run, see freezeExceptAutoModeButton
        inputBlocker.getStyleClass().add("auto-mode-blocker");
        inputBlocker.setCursor(Cursor.WAIT);
        inputBlocker.setVisible(false);
        inputBlocker.addEventFilter(MouseEvent.ANY, Event::consume);
        center.getChildren().add(inputBlocker);
        // keys targeted inside the main area are swallowed while frozen — except Escape, which
        // must reach the global stop handler (Swing AutoModeAction's stop shortcut)
        center.addEventFilter(KeyEvent.ANY, event -> {
            if (inputBlocker.isVisible() && event.getCode() != KeyCode.ESCAPE) {
                event.consume();
            }
        });
        NotificationManagerF.getInstance().attach(center);
        root.setCenter(center);
        root.setBottom(buildStatusBar());

        Scene scene = new Scene(root, 1100, 800);
        ThemeManager.getInstance().manage(scene);
        // colors: register the Swing-parity palette and apply the overrides recorded in
        // colors.json to the managed scene (Swing registers ColorSettings.ColorProperty entries
        // via the static consumers; the FX registry only knows defined properties, so the
        // palette must be loaded before the overrides can be applied at startup)
        ColorPaletteF.ensureRegistered();
        ColorSettingsF.getInstance().applyToScenes();
        // the global action keys of the Swing AutoModeAction (Ctrl+Space starts, Escape stops);
        // an open search bar consumes Escape itself, so it never stops a run while visible.
        // smalldialogs: F1 context help is handled by HelpFacadeF.installAccelerator below —
        // a key-handler branch here would open the page twice.
        scene.setOnKeyPressed(this::handleMainWindowKeyPressed);
        // docking: Ctrl+M maximize toggle (bibliothek CControl.KEY_MAXIMIZE_CHANGE) and the
        // shutdown persistence of the Swing GUIListener.shutDown
        dockingLayout.install(scene);
        // smalldialogs: F1 context help (Swing MainWindow.java:300-302 registers the F1 action)
        HelpFacadeF.installAccelerator(scene);
        // loadingexit (P1): the window close button runs the same exit flow as the Exit menu
        // item (Swing MainWindow.java:366 addWindowListener(exitMainAction.windowListener))
        stage.setOnCloseRequest(e -> {
            e.consume();
            exitApplication();
        });
        stage.setScene(scene);
        stage.show();

        restoreLayout();

        ThemeManager.getInstance().themeProperty().addListener((obs, old, theme) -> updateStatus());
        updateStatus();

        wireSequentView();
        recentFiles.setOnChange(this::updateRecentFilesMenu);
        recentFiles.load();
        // menu: MP7 — honor a persisted non-zero auto-save period at startup (Swing: the saver is
        // active whenever the period is > 0, KeYMediator.java:87 + :148-150); the saver must be
        // armed before the demo load so the load-success selection hands it the proof
        applyAutoSave(ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
                .autoSavePeriod());
        startDemoProofLoad();
        // proofmgmt: the Loaded Proofs view's clicks and the Proof Management dialog route the
        // active-proof switch through the selection model (the Swing mediator path)
        proofManager.setActivationHandler(this::activateProof);
        // proofmgmt: self test hook (independent of the demo load; the verification loads its
        // own examples so that it also runs without key.fx.demo.sequent)
        if (System.getProperty("key.fx.verify.proofmgmt") != null) {
            runProofMgmtVerification();
        }

        // smalldialogs: startup self tests of the ported small dialogs; reports to the log and
        // toast (same pattern as the key.fx.verify.* hooks in startProofLoad). The help facade
        // and the WD load-option panel are proof-independent, so the hooks run at startup rather
        // than after a demo proof load.
        if (System.getProperty("key.fx.verify.help") != null) {
            String report = HelpFacadeF.verifyHelp();
            LOGGER.info("Help verification: {}", report);
            NotificationManagerF.getInstance()
                    .notify("Help verification: " + report,
                        report.endsWith("PASS") ? Kind.INFO : Kind.ERROR);
        }
        if (System.getProperty("key.fx.verify.profileloading") != null) {
            String report = WDLoadOptionPanelF.verifyProfileLoading();
            LOGGER.info("Profile loading verification: {}", report);
            NotificationManagerF.getInstance()
                    .notify("Profile loading verification: " + report,
                        report.endsWith("PASS") ? Kind.INFO : Kind.ERROR);
        }
        // smalldialogs: opens the loading options dialog (Swing KeYFileChooserLoadingOptions
        // accessory) for an interactive check; the selected options are logged when the dialog
        // is confirmed (Enter = Load), Escape/Cancel logs "null"
        if (System.getProperty("key.fx.verify.profileloadingdialog") != null) {
            javafx.application.Platform.runLater(() -> {
                LoadOptions options = LoadingOptionsDialogF.showOptions(stage);
                LOGGER.info("Loading options dialog returned: {}", options);
            });
        }
        // smalldialogs: javac settings provider self test (Swing JavacSettingsProvider); the
        // settings dialog itself is not opened — this checks the read/write round trip
        if (System.getProperty("key.fx.verify.javacsettings") != null) {
            String report = JavacSettingsProviderF.verifyJavacSettings();
            LOGGER.info("Javac settings verification: {}", report);
            NotificationManagerF.getInstance()
                    .notify("Javac settings verification: " + report,
                        report.endsWith("PASS") ? Kind.INFO : Kind.ERROR);
        }
        // colors: P1 parity close-out — Swing-parity palette count, mapped CSS variable wiring
        // and an override round trip (key.fx.verify.colors); proof-independent, so it runs at
        // startup like the other smalldialogs hooks
        if (System.getProperty("key.fx.verify.colors") != null) {
            String report = ColorSettingsF.verifyColors();
            LOGGER.info("Colors verification: {}", report);
            NotificationManagerF.getInstance()
                    .notify("Colors verification: " + report,
                        report.endsWith("PASS") ? Kind.INFO : Kind.ERROR);
        }

        // extension: MP9.0 — register the FX extensions' settings providers into the settings
        // manager registry (Swing SettingsManager registers each KeYGuiExtension.Settings
        // provider at startup) and call the StartupF.init hook of every discovered provider
        // once, at the end of the startup sequence (Swing KeYMediator/ExtensionManager call
        // init right after the window is built; here after the demo load is started so the
        // status-line extensions can observe the selection events of the load).
        for (SettingsProviderF provider : KeYGuiExtensionFacadeF.getSettingsProviders()) {
            SettingsManagerF.getInstance().add(provider);
        }
        KeYGuiExtensionFacadeF.initAll(this, mediator);

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
     * @return the west (left) drawer host of the main window — Proof Tree, Goal List, Loaded
     *         Proofs, Info, Strategy plus the extension left-panel items (used by the drawer
     *         layout verification and the extension verification)
     */
    public DrawerF getWestDrawer() {
        return westDrawer;
    }

    /**
     * @return the east (right) drawer host — currently the Source panel
     */
    public DrawerF getEastDrawer() {
        return eastDrawer;
    }

    /**
     * @return the south (bottom) drawer host; starts empty and is filled by dragging panels
     *         there (cross-port drag and drop)
     */
    public DrawerF getSouthDrawer() {
        return southDrawer;
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
        // strategy (P2a): the Go/Stop button + the parallel-prover merge lock follow the
        // mediator (Swing StrategySelectionView constructor wiring)
        strategyView.attachMediator(mediator);
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
        startProofLoad(location, demo, null, null, false);
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
        startProofLoad(location, demo, proofFilename, null, false);
    }

    /**
     * Loads a proof or problem file, optionally a specific proof out of a proof bundle, with
     * optional loading options.
     *
     * @param location the problem, proof, Java file or proof bundle to load
     * @param demo whether this is the demo property load (notification prefix "Demo proof")
     * @param proofFilename the proof to load relative to the bundle root, or {@code null} if
     *        {@code location} is not a proof bundle
     * @param options the loading options from the {@link LoadingOptionsDialogF} (Swing: the
     *        {@code KeYFileChooserLoadingOptions} accessory consumed by {@code OpenFileAction}),
     *        or {@code null} for the legacy load (recent files, quick load, demo)
     */
    private void startProofLoad(Path location, boolean demo, @Nullable Path proofFilename,
            @Nullable LoadOptions options) {
        startProofLoad(location, demo, proofFilename, options, false);
    }

    /**
     * Loads a proof or problem file, optionally a specific proof out of a proof bundle, with
     * optional loading options and an optional automatic proof run.
     *
     * @param location the problem, proof, Java file or proof bundle to load
     * @param demo whether this is the demo property load (notification prefix "Demo proof")
     * @param proofFilename the proof to load relative to the bundle root, or {@code null} if
     *        {@code location} is not a proof bundle
     * @param options the loading options from the {@link LoadingOptionsDialogF} (Swing: the
     *        {@code KeYFileChooserLoadingOptions} accessory consumed by {@code OpenFileAction}),
     *        or {@code null} for the legacy load (recent files, quick load, demo)
     * @param autoProve whether the automatic prover should run on the loaded proof right after
     *        the load (Swing {@code RunAllProofsAction}: {@code problemLoader.runSynchronously()}
     *        + {@code startAutoMode} + {@code waitWhileAutoMode})
     */
    private void startProofLoad(Path location, boolean demo, @Nullable Path proofFilename,
            @Nullable LoadOptions options, boolean autoProve) {
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
                } else if (options != null) {
                    // smalldialogs: forward the loading options collected by
                    // LoadingOptionsDialogF (Swing OpenFileAction.java:70-76 wires the same
                    // four accessors into the ProblemLoader); force the chosen profile unless
                    // the legacy "Respect profile given in file" mode is active
                    DefaultUserInterfaceControl ui = new DefaultUserInterfaceControl();
                    var loader = new SingleThreadProblemLoader(location, null, null, null, null,
                        false, ui, false, new Properties());
                    loader.forceNewProfileOfNewProofs(options.selectedProfile() != null);
                    loader.setProfileOfNewProofs(options.selectedProfile());
                    loader.setAdditionalProfileOptions(options.additionalProfileOptions());
                    loader.setLoadSingleJavaFile(options.singleJavaFile());
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
                // menu: MP5 — auto prove after the load (Swing RunAllProofsAction: run
                // synchronously, then startAutoMode + waitWhileAutoMode on the
                // MediatorProofControl)
                if (autoProve) {
                    LOGGER.info("Run All Proofs: running auto mode on the loaded proof");
                    env.getProofControl().startAndWaitForAutoMode(env.getLoadedProof());
                    LOGGER.info("Run All Proofs: auto mode finished");
                }
                return env;
            }
        };
        loadTask.setOnSucceeded(event -> {
            KeYEnvironment<DefaultUserInterfaceControl> env = loadTask.getValue();
            // the mediator observes the proof control (auto mode state, closed-goal counter);
            // the UI's own listener refreshes the views after interactive auto mode runs
            mediator.attach(env.getProofControl());
            // menu: MP7 — a freshly attached proof control inherits the persisted Minimize
            // Interaction flag (Swing MinimizeInteraction.updateMainWindow applies the flag to the
            // UI's proof control on construction and on GeneralSettings changes,
            // MinimizeInteraction.java:64-66)
            applyMinimizeInteraction(env.getProofControl());
            // termmenu: give the sequent view the mediator + proof control of the loaded
            // environment so the right-click context menu can be built (Swing parity:
            // CurrentGoalViewMenu is built with the mediator's selected goal and the proof
            // control of the loaded environment)
            sequentView.setMenuContext(mediator, env.getProofControl());
            // prooftree (P3a): the tree popup's Apply Strategy / Prune actions and the
            // auto-mode partial updates need the mediator + proof control (Swing parity:
            // ProofTreeView registers itself as AutoModeListener on the UI's proof control,
            // ProofTreeView.java:532)
            proofTreeView.setActionContext(mediator, env.getProofControl());
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
            // drawer: MP10 — the proof tree is a west drawer item now, not a dockable; expanding
            // it (the sequent is selected in the workspace after the load)
            if (ID_PROOF_TREE.equalsIgnoreCase(show) && westDrawer != null) {
                westDrawer.getItems().stream()
                        .filter(item -> "Proof Tree".equals(item.getButton().getText()))
                        .findFirst().ifPresent(item -> item.getButton().setSelected(true));
                show = ID_SEQUENT;
            }
            String target = ID_SEQUENT;
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
            // smt (P1): run the FX SMT run UI end to end — launch the usable solver union on the
            // first open goal of the demo proof with the auto-applying CLOSE progress mode and
            // check that the goal got closed by the SMT rule application
            if (System.getProperty("key.fx.verify.smt") != null) {
                runSmtVerification();
            }
            // shortcuts (P1): Swing-parity defaults, no collisions, override round trip and the
            // sequent view key path (Ctrl+F shows the search bar)
            if (System.getProperty("key.fx.verify.shortcuts") != null) {
                runShortcutsVerification();
            }
            // inputfreeze (P1): the auto mode freeze — direct freeze/unfreeze with key blocking,
            // then an auto-mode-driven run
            if (System.getProperty("key.fx.verify.inputfreeze") != null) {
                runInputFreezeVerification();
            }
            // sequentmenu (P2a): the left-click term menu + POPUP_DELAY guard, search prefill
            // and the shift+click focussed auto mode
            if (System.getProperty("key.fx.verify.sequentmenu") != null) {
                String report = sequentView.verifySequentMenu();
                LOGGER.info("Sequent menu verification: {}", report);
                NotificationManagerF.getInstance()
                        .notify("Sequent menu verification: " + report,
                            report.endsWith("PASS") || report.startsWith("PASS")
                                    ? Kind.INFO
                                    : Kind.ERROR);
                statusRight.setText(report);
            }
            // dialogs (P2b): the contract-completion dialogs and the lemma dialogs — registry
            // completeness + the contract/auxiliary configurator and lemma selection dialog
            // skeletons + the item chooser semantics
            if (System.getProperty("key.fx.verify.dialogs") != null) {
                String report = DialogsVerifyF.run(stage, selectionModel.getSelectedProof(),
                    userInterface);
                statusRight.setText(report);
            }
            if (System.getProperty("key.fx.verify.prooftree") != null
                    && System.getProperty("key.fx.demo.autoprove.live") == null) {
                // prooftree (P3a): the C19-C23/C25/C27 self test — per-proof view states,
                // linearized mode, OSS protocol rows, whole-tree expand/collapse, node-filter
                // counting and the notes/statistics popup dialogs. Skipped when the live demo
                // auto-prover runs in parallel (the auto-mode-stop dispatch below verifies the
                // final tree instead — running the self test against a proof the prover is
                // still mutating would race with the structural events)
                String report = ProofTreeVerifyF.run(stage, selectionModel.getSelectedProof(),
                    proofTreeView);
                statusRight.setText(report);
            }
            // loadingexit (P1): recent-files round trip with loading options + profile
            // resolution, then the exit flow — the window close button path with Confirm Exit
            // off must terminate the process with exit code 0
            if (System.getProperty("key.fx.verify.loadingexit") != null) {
                runLoadingExitVerification();
            }
            // drawer: headless self test of the DrawerF port (exclusive/multiselect semantics,
            // side placement, button-order split, drag-and-drop reorder + transfer seams)
            if (System.getProperty("key.fx.verify.drawer") != null) {
                String drawerReport = DrawerF.selfTest();
                LOGGER.info("Drawer verification: {}", drawerReport);
                NotificationManagerF.getInstance()
                        .notify("Drawer verification: " + drawerReport,
                            drawerReport.startsWith("PASS") ? Kind.INFO : Kind.ERROR);
            }
            // drawer: MP10 — headless self test of the drawered main area (drawer hosts, item
            // sets, default expansions and the drag-and-drop seams on the live drawers)
            if (System.getProperty("key.fx.verify.drawerlayout") != null) {
                runDrawerLayoutVerification(env);
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
            // smalldialogs: soundiness report self test (Swing SoundinessDialog/
            // SoundinessAnalyzer), runs on the freshly loaded demo proof and opens the dialog
            if (System.getProperty("key.fx.verify.soundiness") != null) {
                runSoundinessVerification();
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
            // cancel keeps the proof, seam dispatch opens the dialog, apply adds to the proof)
            // after the demo load; termmenu/S4 passes the seam so the dispatch path
            // (WindowUserInterfaceControlF.completeAndApplyTacletMatch) is covered
            if (System.getProperty("key.fx.verify.tacletmatch") != null) {
                TacletMatchVerifyF.runTacletMatchVerification(env.getLoadedProof(),
                    env.getProofControl(), stage, mediator.getNotationInfo(),
                    getUserInterfaceControl());
            }
            // lemmaorigin: begin — term labels / origin visualizer / lemma generator self test
            if (System.getProperty("key.fx.verify.lemmaorigin") != null) {
                String report = OriginLabelsF.verify(this);
                LOGGER.info("Lemmaorigin verification: {}", report);
                NotificationManagerF.getInstance()
                        .notify("Lemmaorigin verification: " + report,
                            report.contains("FAIL") ? Kind.ERROR : Kind.INFO);
            }
            // lemmaorigin: end
            // termmenu: run the headless sequent context-menu self test
            // (key.fx.verify.termmenu) after the demo load like the other proof-dependent
            // verify hooks; the text report goes to stdout
            if (System.getProperty("key.fx.verify.termmenu") != null) {
                runTermMenuVerification(env);
            }
            // menu: MP8 — term-menu wiring self test (key.fx.verify.termmenuwiring), same seam
            // as key.fx.verify.termmenu: asserts the MP8a/MP8b wiring on the loaded demo — the
            // focus_auto_mode item is ENABLED with a non-null action handler and the
            // macro_menu section exists with exactly the four AUTOMATION_MACROS names. The
            // handlers are NOT invoked (a real focused auto mode / macro run is too heavy
            // mid-regression); enablement + handler presence is the assertion.
            if (System.getProperty("key.fx.verify.termmenuwiring") != null) {
                runTermMenuWiringVerification(env);
            }
            // menu: MP1/MP3c — menu parity self test (key.fx.verify.menuparity): walks the
            // built menu bar and asserts the Proof menu entries against the Swing
            // createProofMenu table and (since MP3c) the View menu entries against the Swing
            // createViewMenu table; each marker line must end with PASS
            if (System.getProperty("key.fx.verify.menuparity") != null) {
                verifyMenuParity();
            }
            // menu: MP7 — Minimize Interaction self test (key.fx.verify.minimizeinteraction):
            // flips the persisted taclet filter through the same apply helper the toggle uses and
            // asserts the proof control mirrors the flag in both directions
            if (System.getProperty("key.fx.verify.minimizeinteraction") != null) {
                GeneralSettings gs = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
                boolean original = gs.getTacletFilter();
                boolean ok;
                gs.setTacletFilter(!original);
                applyMinimizeInteraction(env.getProofControl());
                ok = env.getProofControl().isMinimizeInteraction() == gs.getTacletFilter();
                gs.setTacletFilter(original);
                applyMinimizeInteraction(env.getProofControl());
                ok &= env.getProofControl().isMinimizeInteraction() == gs.getTacletFilter();
                LOGGER.info("Minimize interaction verification: {}", ok ? "PASS" : "FAIL");
                NotificationManagerF.getInstance()
                        .notify("Minimize interaction verification: " + (ok ? "PASS" : "FAIL"),
                            ok ? Kind.INFO : Kind.ERROR);
            }
            // menu: MP7 — right-click macro popup self test (key.fx.verify.rightclickmacro):
            // builds the popup through the SequentViewF seam with the flag ON and OFF and asserts
            // the macro names / the term-menu fallback (report logged/toasted there)
            if (System.getProperty("key.fx.verify.rightclickmacro") != null) {
                String report = sequentView.verifyRightClickMacro();
                LOGGER.info("Right-click macro verification: {}", report);
                NotificationManagerF.getInstance()
                        .notify("Right-click macro verification: " + report,
                            report.endsWith("PASS") ? Kind.INFO : Kind.ERROR);
            }
            // menu: MP7 — auto-save self test (key.fx.verify.autosave): asserts the saver is armed
            // iff the persisted period is > 0 and that it received the loaded proof (the proof
            // identity is read reflectively; see readAutoSaveProof)
            if (System.getProperty("key.fx.verify.autosave") != null) {
                GeneralSettings gs = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
                int savedPeriod = gs.autoSavePeriod();
                boolean ok;
                try {
                    // the startup arming must match the persisted period (armed iff > 0)
                    boolean armedOk =
                        (mediator.getAutoSaver() != null) == (savedPeriod > 0);
                    // force the armed state and route the loaded proof again through the real
                    // selection path, so the saver's setProof fires (mediator.setProof hook)
                    gs.setAutoSave(DEFAULT_AUTO_SAVE_PERIOD);
                    applyAutoSave(DEFAULT_AUTO_SAVE_PERIOD);
                    selectionModel.setSelectedProof(null);
                    selectionModel.setSelectedProof(env.getLoadedProof());
                    AutoSaver saver = mediator.getAutoSaver();
                    boolean proofOk =
                        saver != null && readAutoSaveProof(saver) == env.getLoadedProof();
                    // the disarmed state after the switch
                    gs.setAutoSave(0);
                    applyAutoSave(0);
                    ok = armedOk && proofOk && mediator.getAutoSaver() == null;
                } finally {
                    gs.setAutoSave(savedPeriod);
                    applyAutoSave(savedPeriod);
                }
                LOGGER.info("Auto save verification: {}", ok ? "PASS" : "FAIL");
                NotificationManagerF.getInstance()
                        .notify("Auto save verification: " + (ok ? "PASS" : "FAIL"),
                            ok ? Kind.INFO : Kind.ERROR);
            }
            // extension: MP9.0 — extension SPI self test (key.fx.verify.extensions): asserts
            // the facade discovery (3 registered FX extensions), the two status-line controls
            // in the built status bar, the Heatmap menu in the menu bar, the Heatmap settings
            // provider in the settings registry and the term-menu extension section falling
            // back to the disabled placeholder without a position. One stdout report line.
            if (System.getProperty("key.fx.verify.extensions") != null) {
                runExtensionVerification(env);
            }
            if (System.getProperty("key.fx.demo.autoprove.live") != null) {
                startLiveAutoMode(env);
            }
        });
        loadTask.setOnFailed(event -> {
            Throwable error = loadTask.getException();
            String message = (demo ? "Demo proof" : "Proof") + " loading failed";
            LOGGER.error(message, error);
            // seam: loading errors surface in the IssueDialog (Swing parity: the
            // ProblemLoader branch of WindowUserInterfaceControl.taskFinishedInternal,
            // WindowUserInterfaceControl.java:236-244, calls IssueDialog.showExceptionDialog;
            // the FX load task throws instead of reporting a failed TaskFinishedInfo)
            IssueDialogF.showExceptionDialog(getStage(), error);
            // notification: termmenu/S4 — route the failure through the notification center
            // instead of the plain toast (Swing parity: the ExceptionFailureEvent framework,
            // NotificationManager.setDefaultNotification + the FIXME'd
            // ExceptionFailureNotification; the FX ExceptionFailureNotificationF is toast-only,
            // so the Swing double-dialog concern does not apply and it is a default task).
            // The IssueDialog above stays the primary surface; the center's toast is the
            // notification sink.
            NotificationCenterF.getInstance().handleNotificationEvent(
                new ExceptionFailureEventF(message, error));
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
        // smalldialogs: loading options (Swing KeYFileChooserLoadingOptions accessory, read by
        // OpenFileAction on approve, OpenFileAction.java:70-76). The JavaFX FileChooser has no
        // accessory, so the options are collected in a pre-load dialog; Cancel aborts the load
        // like the Swing chooser cancel. Proof bundles keep the profile of the bundle (Swing
        // OpenFileAction returns before the options wiring), so no dialog for them.
        if (!ProofSelectionDialogF.isProofBundle(file.toPath())) {
            LoadOptions options = LoadingOptionsDialogF.showOptions(stage);
            if (options == null) {
                return;
            }
            openProofFile(file.toPath(), options);
            return;
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
        openProofFile(file, null);
    }

    /**
     * Loads the given file with the given loading options and registers it in the recent files
     * list. The options come from the {@link LoadingOptionsDialogF} in {@code
     * openFileChooser()} (Swing: the {@code KeYFileChooserLoadingOptions} accessory); the
     * recent-files and quick-load flows keep the legacy behavior (no options, like Swing where
     * the accessory only exists in the file chooser).
     *
     * @param file the file to load
     * @param options the loading options, or {@code null} for the legacy load
     */
    public void openProofFile(Path file, @Nullable LoadOptions options) {
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
        // loadingexit (P1): remember the loading options with the entry (Swing
        // WindowUserInterfaceControl.loadProblem registers problemLoader.getProfileOfNewProofs()
        // / isLoadSingleJavaFile() / getAdditionalProfileOptions, WindowUserInterfaceControl
        // .java:102-105); the recent-files menu restores them on open
        recentFiles.add(file.toAbsolutePath().toString(),
            options != null && options.selectedProfile() != null
                    ? options.selectedProfile().ident()
                    : null,
            options != null && options.singleJavaFile(),
            options != null ? options.additionalProfileOptions() : null);
        startProofLoad(file, false, null, options);
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
     * menu: MP5 — the Edit Last Opened File action (Swing {@code EditMostRecentFileAction}): opens
     * the most recently opened file with the default external editor. The Swing original goes
     * through {@code EditFileActionHandler.workWithFile} (finally {@code Desktop.open}); the FX
     * port opens the file's {@code file://} URI through the {@link HelpFacadeF} browser seam
     * (host services), so the same seam that serves the About-menu browser actions is reused.
     */
    private void editLastOpenedFile() {
        String recent = recentFiles.getMostRecent();
        if (recent == null) {
            // the item is disabled without a recent file; keep the Swing action's silent guard
            return;
        }
        HelpFacadeF.openExternal(Path.of(recent).toUri().toString());
    }

    // ------------------------------------------------------------------
    // menu: MP5 — taclet loading / proving (Swing LemmaGenerationAction)
    // ------------------------------------------------------------------

    /**
     * menu: MP5 — the "Load User Defined Taclets…" action (Swing
     * {@code LemmaGenerationAction.ProveAndAddTaclets}, Mode.LOAD): loads the taclets of a
     * user-chosen {@code .key} file into the current proof. The {@code TacletSoundnessPOLoader}
     * runs the soundness proof obligations; on success the loaded taclets are prepended to the
     * proof's init config and added to its open goals (the Swing doStopped flow,
     * LemmaGenerationAction.java:307-326).
     */
    private void loadUserDefinedTaclets() {
        Proof proof = selectionModel.getSelectedProof();
        if (proof == null) {
            return; // the item is disabled without a proof (Swing proofIsRequired()==true)
        }
        Optional<LoadUserTacletsDialogF.Result> result =
            LoadUserTacletsDialogF.showDialog(stage, LoadUserTacletsDialogF.Mode.LOAD);
        if (result.isEmpty()) {
            return;
        }
        Path fileForTaclets = result.get().fileForTaclets();
        boolean loadAsLemmata = result.get().generateProofObligations();
        // lemma (P2b, A3): the axiom files chosen in the dialog are loaded for the lemmata only
        List<Path> filesForAxioms = result.get().filesForAxioms();
        final WindowUserInterfaceControlF ui = getUserInterfaceControl();
        Profile profile = proof.getServices().getProfile();
        ProblemInitializer problemInitializer =
            new ProblemInitializer(ui, new Services(profile), ui);
        TacletLoader tacletLoader = new TacletLoader.TacletFromFileLoader(ui, ui,
            problemInitializer, fileForTaclets, filesForAxioms, proof.getInitConfig().copy());

        LemmaLoaderListener listener = new LemmaLoaderListener() {
            @Override
            protected void doStopped(Throwable exception) {
                handleTacletLoadException(exception);
            }

            @Override
            protected void doStopped(@Nullable ProofAggregate p, ImmutableSet<Taclet> taclets,
                    boolean addAxioms) {
                // menu: getMediator().startInterface(true) is a no-op — the FX port has no
                // interface lock (KeYMediatorF has no startInterface/stopInterface)
                if (p != null) {
                    ui.registerProofAggregate(p);
                }
                if (p != null || addAxioms) {
                    // add only the taclets to the goals if the proof obligations were added
                    // successfully (Swing LemmaGenerationAction.java:314-326)
                    ImmutableList<Taclet> base = proof.getInitConfig().getTaclets();
                    base = base.prependReverse(taclets);
                    proof.getInitConfig().setTaclets(base);
                    for (Taclet taclet : taclets) {
                        for (Goal goal : proof.openGoals()) {
                            goal.addTaclet(taclet, SVInstantiations.EMPTY_SVINSTANTIATIONS, false);
                        }
                    }
                }
            }
        };
        // LOAD mode: the loaded taclets are only used for the current proof, not for proving
        // (isOnlyUsedForProvingTaclets=false); the loader works on a copy of the proof's init
        // config (Swing LemmaGenerationAction.java:295, :331-333)
        runTacletSoundnessLoader(tacletLoader, proof.getInitConfig(), loadAsLemmata, false,
            listener);
    }

    /**
     * menu: MP5 — the "Load User Defined Taclets for Proving" action (Swing
     * {@code LemmaGenerationAction.ProveUserDefinedTaclets}, Mode.PROVE): creates proof
     * obligations for the taclets of a user-chosen file without loading them into the current
     * proof. The created proofs are registered (they appear in the Loaded Proofs view) and the
     * first proof is selected, like the Swing doStopped (LemmaGenerationAction.java:231-240).
     */
    private void proveUserDefinedTaclets() {
        Optional<LoadUserTacletsDialogF.Result> result =
            LoadUserTacletsDialogF.showDialog(stage, LoadUserTacletsDialogF.Mode.PROVE);
        if (result.isEmpty()) {
            return;
        }
        Path fileForTaclets = result.get().fileForTaclets();
        boolean loadAsLemmata = result.get().generateProofObligations();
        // lemma (P2b, A3): the axiom files chosen in the dialog are loaded for the lemmata only
        List<Path> filesForAxioms = result.get().filesForAxioms();
        final WindowUserInterfaceControlF ui = getUserInterfaceControl();
        Profile profile = lastEnvironment != null ? lastEnvironment.getProfile()
                : AbstractProfile.getDefaultProfile();
        ProblemInitializer problemInitializer =
            new ProblemInitializer(ui, new Services(profile), ui);
        TacletLoader tacletLoader = new TacletLoader.TacletFromFileLoader(ui, ui,
            problemInitializer, profile, fileForTaclets, filesForAxioms);

        LemmaLoaderListener listener = new LemmaLoaderListener() {
            @Override
            protected void doStopped(Throwable exception) {
                handleTacletLoadException(exception);
            }

            @Override
            protected void doStopped(@Nullable ProofAggregate p, ImmutableSet<Taclet> taclets,
                    boolean addAxioms) {
                // menu: getMediator().startInterface(true) is a no-op (see loadUserDefinedTaclets)
                if (p != null) {
                    ui.registerProofAggregate(p);
                    selectionModel.setSelectedProof(p.getFirstProof());
                }
            }
        };
        // PROVE mode: only used for proving (isOnlyUsedForProvingTaclets=true), original config
        // from the fresh proof environment (Swing LemmaGenerationAction.java:244-246)
        runTacletSoundnessLoader(tacletLoader,
            tacletLoader.getProofEnvForTaclets().getInitConfigForEnvironment(), loadAsLemmata,
            true, listener);
    }

    /**
     * menu: MP5 — the "Load KeY Taclets" action (Swing {@code LemmaGenerationAction
     * .ProveKeYTaclets}): creates proof obligations for the system taclets of the profile
     * (Swing LemmaGenerationAction.java:137-168).
     */
    private void proveKeYTaclets() {
        final WindowUserInterfaceControlF ui = getUserInterfaceControl();
        Profile profile = lastEnvironment != null ? lastEnvironment.getProfile()
                : AbstractProfile.getDefaultProfile();
        TacletLoader tacletLoader = new TacletLoader.KeYsTacletsLoader(ui, ui, profile);

        LemmaLoaderListener listener = new LemmaLoaderListener() {
            @Override
            protected void doStopped(Throwable exception) {
                handleTacletLoadException(exception);
            }

            @Override
            protected void doStopped(@Nullable ProofAggregate p, ImmutableSet<Taclet> taclets,
                    boolean addAxioms) {
                // menu: getMediator().startInterface(true) is a no-op (see loadUserDefinedTaclets)
                if (p != null) {
                    ui.registerProofAggregate(p);
                }
            }
        };
        // KeY mode: the system taclets always get proof obligations (Swing passes the literal
        // true, LemmaGenerationAction.java:163-165)
        runTacletSoundnessLoader(tacletLoader,
            tacletLoader.getProofEnvForTaclets().getInitConfigForEnvironment(), true, true,
            listener);
    }

    /**
     * menu: MP5 — the "Lemma Generation (Batch Mode)" info dialog (Swing
     * {@code LemmaGenerationBatchModeAction.actionPerformed}: {@code JOptionPane} with the
     * batch-mode {@link #BATCH_MODE_TEXT} description).
     */
    private void showLemmaGenerationBatchMode() {
        Alert alert = new Alert(Alert.AlertType.INFORMATION);
        alert.setTitle("Using the Batch Mode for Proving Taclets");
        alert.setHeaderText(null);
        TextArea text = new TextArea(BATCH_MODE_TEXT);
        text.setEditable(false);
        text.setWrapText(true);
        alert.getDialogPane().setContent(text);
        alert.initOwner(stage);
        ExampleChooserF.themeDialogPane(alert);
        alert.showAndWait();
    }

    /**
     * menu: MP5 — the "Run All Proofs" action (Swing {@code RunAllProofsAction}, behind the
     * {@code BULK_UI_TEST} feature flag): loads the proof named by the
     * {@link RunAllProofsF#ENV_VARIABLE} environment variable (or system property) and
     * auto-proves it; without a usable spec a short usage/status message is shown (the Swing
     * multi-file batch loop is not ported, see {@link RunAllProofsF}).
     */
    private void runAllProofs() {
        Path proofFile = RunAllProofsF.proofToRun();
        if (proofFile == null) {
            popupWarning(RunAllProofsF.usageMessage());
            return;
        }
        LOGGER.info("Run All Proofs: loading and auto-proving {}", proofFile);
        startProofLoad(proofFile, false, null, null, true);
    }

    /**
     * menu: MP5 — shared failure handling of the taclet loaders (Swing
     * {@code LemmaGenerationAction.handleException}): the exception surfaces in the issue
     * dialog.
     */
    private void handleTacletLoadException(Throwable exception) {
        LOGGER.error("Taclet loading failed", exception);
        IssueDialogF.showExceptionDialog(getStage(), exception);
    }

    /**
     * menu: MP5 — builds and starts a {@link TacletSoundnessPOLoader} with the shared
     * "supported taclets only" filter (the default of the not-ported Swing
     * {@code LemmaSelectionDialog}).
     *
     * @param tacletLoader the loader of the candidate taclets
     * @param originalConfig the init config the proof obligations are based on
     * @param loadAsLemmata whether proof obligations are generated (the dialog's "Generate proof
     *        obligations for taclets" checkbox, Swing {@code isGenerateProofObligations})
     * @param isOnlyUsedForProvingTaclets whether the taclets are only used for proving (PROVE/
     *        KeY mode) or also added to the current proof (LOAD mode)
     * @param listener the FX-side loader listener (stopped callbacks are marshalled to the FX
     *        thread)
     */
    private void runTacletSoundnessLoader(TacletLoader tacletLoader, InitConfig originalConfig,
            boolean loadAsLemmata, boolean isOnlyUsedForProvingTaclets,
            LemmaLoaderListener listener) {
        // lemma (P2b, A2): the Swing LemmaSelectionDialog is the taclet filter — the user picks
        // the taclets the soundness proof obligations are created for (the hardcoded
        // "supported taclets only" default of the MP5 port is gone); it defaults to the same
        // behavior while "Show only supported taclets." is active and everything is left on the
        // choice side
        TacletSoundnessPOLoader.TacletFilter filter = new LemmaSelectionDialogF();
        TacletSoundnessPOLoader loader = new TacletSoundnessPOLoader(listener, filter,
            loadAsLemmata, tacletLoader, originalConfig, isOnlyUsedForProvingTaclets);
        loader.start();
    }

    /**
     * menu: MP5 — the loader listener of the taclet flows (Swing
     * {@code LemmaGenerationAction.AbstractLoaderListener}): forwards the progress callbacks to
     * the window's user interface control and marshals the stopped callbacks to the FX thread
     * (the {@code TacletSoundnessPOLoader} runs on its own thread).
     */
    private abstract class LemmaLoaderListener implements TacletSoundnessPOLoader.LoaderListener {

        @Override
        public void started() {
            // menu: Swing AbstractLoaderListener.started() calls mediator.stopInterface(true) to
            // lock the interface; the FX port has no interface lock, so this is a no-op
        }

        @Override
        public void progressStarted(Object sender) {
            getUserInterfaceControl().progressStarted(sender);
        }

        @Override
        public void reportStatus(Object sender, String status) {
            getUserInterfaceControl().reportStatus(sender, status);
        }

        @Override
        public void resetStatus(Object sender) {
            getUserInterfaceControl().resetStatus(sender);
        }

        @Override
        public final void stopped(@Nullable ProofAggregate p, ImmutableSet<Taclet> taclets,
                boolean addAsAxioms) {
            FxUtil.runLater(() -> doStopped(p, taclets, addAsAxioms));
        }

        @Override
        public final void stopped(Throwable exception) {
            FxUtil.runLater(() -> doStopped(exception));
        }

        protected abstract void doStopped(@Nullable ProofAggregate p,
                ImmutableSet<Taclet> taclets, boolean addAsAxioms);

        protected abstract void doStopped(Throwable exception);
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
            // loadingexit (P1): restore the entry's profile / single-java loading options on
            // open (Swing RecentFileAction.actionPerformed, RecentFileMenu.java:386-427)
            recentFilesMenu.getItems()
                    .add(menuItem(text, () -> openRecentFile(entry)));
        }
        // P3b/B18: Swing leaves the empty recent-files submenu ENABLED (it just shows nothing):
        // RecentFileMenu's constructor does not disable it (the effect of the commented-out line
        // RecentFileMenu.java:78) and setEnabled(getItemCount() != 0) in addRecentFileNoSave
        // (:144) only ever runs after an entry was inserted. Do the same here — no setDisable.
    }

    /**
     * loadingexit (P1) — opens a recent-files entry with its stored loading options (Swing
     * {@code RecentFileAction.actionPerformed}, RecentFileMenu.java:386-427): proof bundles show
     * the proof selection dialog; other files resolve the stored profile ident through the
     * {@code DefaultProfileResolver} services (a missing profile warns like the Swing
     * {@code JOptionPane}) and load with the resolved profile, its additional profile options
     * and the single-java flag.
     */
    private void openRecentFile(RecentFilesF.Entry entry) {
        Path file = Path.of(entry.path());

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

        String profileName = entry.profile();
        // A missing profile -- null, or the literal string "null" that older recent-file
        // entries stored for it -- means "use the default profile", not an error.
        boolean hasProfile = profileName != null && !profileName.equals("null");
        Profile profile = null;
        if (hasProfile) {
            profile = ServiceLoader.load(DefaultProfileResolver.class).stream()
                    .filter(it -> it.get().getProfileName().equals(profileName)).findFirst()
                    .map(it -> it.get().getDefaultProfile()).orElse(null);
            if (profile == null) {
                Alert alert = new Alert(AlertType.WARNING,
                    "Could not find previous selected profile %s.".formatted(profileName),
                    ButtonType.OK);
                alert.setTitle("Recent File");
                alert.setHeaderText(null);
                alert.initOwner(stage);
                alert.showAndWait();
                return;
            }
        }
        LoadOptions options = hasProfile || entry.singleJava()
                ? new LoadOptions(profile, entry.additionalOption(), entry.singleJava())
                : null;
        openProofFile(file, options);
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
                    if (System.getProperty("key.fx.verify.prooftree") != null) {
                        // prooftree (P3a): re-run the C19-C23/C25/C27 self test after a live
                        // auto mode — the tree listeners already applied the C27 partial subtree
                        // updates on the auto mode stop, so the counter report shows them
                        String report = ProofTreeVerifyF.run(stage,
                            selectionModel.getSelectedProof(), proofTreeView);
                        LOGGER.info("Proof tree verification (after live auto mode): {}", report);
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
     * shortcuts (P1): runs the shortcut verification ({@code key.fx.verify.shortcuts}): the
     * re-mapped defaults match the Swing table (KeyStrokeSettings.java:60-106), no two
     * registered actions share a keystroke (the old FX defaults collided: OneStep/AutoMode both
     * Ctrl+SPACE, TryClose/Copy both Ctrl+C), an explicit user override still wins over the
     * defaults (bind round trip, restored), and the sequent view's Ctrl+F handler shows the
     * search bar.
     */
    private void runShortcutsVerification() {
        ArrayList<String> failures = new ArrayList<>();
        KeyStrokeManagerF manager = KeyStrokeManagerF.getInstance();
        // compared in the shared Swing spec format (the effective end state: defaults merged
        // with the persisted keystrokes.json, which is shared with the Swing UI)
        String[][] expected = {
            { "de.uka.ilkd.key.macros.FullAutoPilotProofMacro", "shift ctrl pressed V" },
            { "de.uka.ilkd.key.macros.OneStepProofMacro", "shift ctrl pressed SPACE" },
            { "de.uka.ilkd.key.macros.TryCloseMacro", "shift ctrl pressed C" },
            { "de.uka.ilkd.key.gui.actions.SearchInProofTreeAction", "shift ctrl pressed F" },
            { "de.uka.ilkd.key.gui.actions.SearchInSequentAction", "ctrl pressed F" },
            { "de.uka.ilkd.key.gui.actions.SearchNextAction", "pressed F3" },
            { "de.uka.ilkd.key.gui.actions.SearchPreviousAction", "shift pressed F3" },
            { "de.uka.ilkd.key.gui.actions.CopyToClipboardAction", "ctrl pressed C" },
            { "de.uka.ilkd.key.gui.actions.GoalSelectAboveAction", "ctrl pressed K" },
            { "de.uka.ilkd.key.gui.actions.GoalSelectBelowAction", "ctrl pressed J" },
            { "de.uka.ilkd.key.gui.actions.GoalBackAction", "ctrl pressed Z" },
            { "de.uka.ilkd.key.gui.actions.PruneProofAction", "ctrl pressed DELETE" },
            { "de.uka.ilkd.key.gui.actions.AutoModeAction", "ctrl pressed SPACE" },
            { "de.uka.ilkd.key.gui.actions.PrettyPrintToggleAction", "shift ctrl pressed P" } };
        Map<String, String> snapshot = manager.snapshot();
        for (String[] entry : expected) {
            String actual = snapshot.get(entry[0]);
            if (!entry[1].equals(actual)) {
                failures.add(entry[0] + ": " + actual + " != " + entry[1]);
            }
        }
        // no two registered actions may share one keystroke (the old FX defaults collided:
        // OneStep/AutoMode both Ctrl+SPACE, TryClose/Copy both Ctrl+C)
        HashSet<String> seen = new HashSet<>();
        for (String spec : snapshot.values()) {
            if (!seen.add(spec)) {
                failures.add("duplicate binding: " + spec);
            }
        }
        // an explicit user override still wins over the defaults (bind round trip, restored)
        KeyCombination original =
            manager.binding("de.uka.ilkd.key.gui.actions.CopyToClipboardAction")
                    .orElseThrow();
        manager.bind("de.uka.ilkd.key.gui.actions.CopyToClipboardAction",
            KeyCombination.valueOf("Shortcut+Shift+C"));
        if (!"shift ctrl pressed C".equals(manager.snapshot()
                .get("de.uka.ilkd.key.gui.actions.CopyToClipboardAction"))) {
            failures.add("override round trip: bind() did not take effect");
        }
        manager.bind("de.uka.ilkd.key.gui.actions.CopyToClipboardAction", original);
        // sequent view key path: Ctrl+F shows the search bar (SearchInSequentAction)
        sequentView.fireEvent(new KeyEvent(KeyEvent.KEY_PRESSED, "", "f", KeyCode.F, false, true,
            false, false));
        if (!sequentView.isSearchBarShowing()) {
            failures.add("Ctrl+F did not show the sequent search bar");
        }
        String report = failures.isEmpty()
                ? "PASS (defaults, no collisions, override round trip, sequent key path)"
                : "FAIL: " + String.join("; ", failures);
        LOGGER.info("Shortcuts verification: {}", report);
        NotificationManagerF.getInstance()
                .notify("Shortcuts verification: " + report,
                    report.startsWith("PASS") ? Kind.INFO : Kind.ERROR);
        statusRight.setText(report);
    }

    /**
     * inputfreeze (P1): runs the input-freeze verification ({@code key.fx.verify.inputfreeze}):
     * (1) the deterministic freeze/unfreeze — the blocking overlay shows, a fired Ctrl+F key
     * event is blocked while frozen and shows the search bar after the unfreeze (input
     * restored); (2) the listener-driven path — an auto mode run started via the mediator
     * freezes the views and the stop (requested or natural) unfreezes them.
     */
    private void runInputFreezeVerification() {
        ArrayList<String> failures = new ArrayList<>();
        // 1. deterministic freeze/unfreeze (the mechanism the auto mode listener drives)
        freezeExceptAutoModeButton();
        if (!inputBlocker.isVisible()) {
            failures.add("freezeExceptAutoModeButton: overlay not visible");
        } else {
            sequentView.fireEvent(new KeyEvent(KeyEvent.KEY_PRESSED, "", "f", KeyCode.F, false,
                true, false, false));
            if (sequentView.isSearchBarShowing()) {
                failures.add("key input not blocked while frozen (Ctrl+F showed the search bar)");
                sequentView.fireEvent(new KeyEvent(KeyEvent.KEY_PRESSED, "", "",
                    KeyCode.ESCAPE, false, false, false, false));
            }
        }
        unfreezeExceptAutoModeButton();
        if (inputBlocker.isVisible()) {
            failures.add("unfreezeExceptAutoModeButton: overlay still visible");
        }
        sequentView.fireEvent(new KeyEvent(KeyEvent.KEY_PRESSED, "", "f", KeyCode.F, false, true,
            false, false));
        if (!sequentView.isSearchBarShowing()) {
            failures.add("key input not restored after the unfreeze");
        } else {
            // close the search bar for a clean state
            sequentView.fireEvent(new KeyEvent(KeyEvent.KEY_PRESSED, "", "", KeyCode.ESCAPE,
                false, false, false, false));
        }
        // 2. the listener-driven path: an auto mode run must freeze the views (polled on the FX
        // thread; the auto mode run may finish on its own before the stop is requested)
        mediator.startAutoMode();
        Boolean[] sawFrozen = { false };
        Integer[] ticks = { 0 };
        Timeline[] holder = new Timeline[1];
        holder[0] = new Timeline(new KeyFrame(Duration.millis(100), event -> {
            if (inputBlocker.isVisible()) {
                sawFrozen[0] = true;
            }
            boolean running = mediator.autoModeRunningProperty().get();
            if (running && ++ticks[0] < 120) {
                return; // keep polling (max ~12 s), then request the stop
            }
            holder[0].stop();
            if (running) {
                mediator.stopAutoMode();
                Timeline post = new Timeline(new KeyFrame(Duration.millis(500), ev -> {
                    if (inputBlocker.isVisible()) {
                        failures.add("the overlay stayed visible after stopAutoMode");
                    }
                    reportInputFreeze(failures, sawFrozen[0]);
                }));
                post.play();
                return;
            }
            // the run finished on its own: the overlay must be hidden again
            if (sawFrozen[0] && !inputBlocker.isVisible()) {
                LOGGER.info("inputfreeze: auto-mode-driven freeze/unfreeze observed");
            } else if (!sawFrozen[0]) {
                LOGGER.info(
                    "inputfreeze: the auto mode run ended before the freeze could be observed (the listener wiring is covered by the direct test)");
            } else {
                failures.add("the overlay stayed visible after the auto mode stop");
            }
            reportInputFreeze(failures, sawFrozen[0]);
        }));
        holder[0].setCycleCount(Timeline.INDEFINITE);
        holder[0].play();
    }

    /** inputfreeze (P1): logs and reports the freeze verification result. */
    private void reportInputFreeze(ArrayList<String> failures, boolean sawFrozen) {
        String report = failures.isEmpty()
                ? "PASS (freeze/unfreeze" + (sawFrozen ? " + auto-mode-driven freeze)" : ")")
                : "FAIL: " + String.join("; ", failures);
        LOGGER.info("Input freeze verification: {}", report);
        NotificationManagerF.getInstance()
                .notify("Input freeze verification: " + report,
                    report.startsWith("PASS") ? Kind.INFO : Kind.ERROR);
        statusRight.setText(report);
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
     * smt (P1): runs the FX SMT run UI end to end ({@code key.fx.verify.smt}), run after the
     * demo load like the other proof-dependent verify hooks: launches the first usable solver
     * union on the first open goal with the auto-applying {@code ProgressMode.CLOSE} (the
     * {@link SolverListenerF} closes the goal via the SMT rule on completion) and checks the
     * solver result and the closed goal. The waiting happens on a background thread (the hook
     * itself is invoked on the FX thread; the modal progress dialog stays interactive).
     */
    private void runSmtVerification() {
        Thread thread = new Thread(this::runSmtVerificationAsync, "SMTVerify");
        thread.setDaemon(true);
        thread.start();
    }

    private void runSmtVerificationAsync() {
        String report;
        Proof proof = mediator.getSelectedProof();
        ProofIndependentSMTSettings smtSettings =
            ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings();
        Collection<SolverTypeCollection> unions = smtSettings.getUsableSolverUnions();
        if (proof == null || proof.closed() || unions.isEmpty()) {
            report = "FAIL: no open proof or no usable solver union (unions=" + unions.size()
                + ")";
        } else {
            Goal goal = proof.openGoals().iterator().next();
            SolverTypeCollection union = unions.iterator().next();
            // the CLOSE progress mode auto-applies the results on completion (and closes the
            // goals); snapshot + restore so the user's setting is not persisted
            ProgressMode previousMode = smtSettings.getModeOfProgressDialog();
            smtSettings.setModeOfProgressDialog(ProgressMode.CLOSE);
            SMTProblem problem = new SMTProblem(goal);
            SolverListenerF.launch(mediator, getStage(), proof, List.of(problem),
                union.getTypes());
            // SolverLauncher.launch blocks its background thread until every solver finished
            // and the CLOSE auto-apply is posted afterwards (FIFO on the FX thread): poll for
            // the closed goal (the solvers are quick on the demo problem)
            long deadline = System.currentTimeMillis() + 120_000;
            while (System.currentTimeMillis() < deadline && !goal.node().isClosed()) {
                try {
                    Thread.sleep(500);
                } catch (InterruptedException e) {
                    Thread.currentThread().interrupt();
                    break;
                }
            }
            boolean closed = goal.node().isClosed();
            if (!closed) {
                // discard the still open modal dialog so the verify run does not stall
                Platform.runLater(SolverListenerF::discardCurrentDialog);
            }
            report = (closed ? "PASS" : "FAIL") + " (union=" + union + ", goalClosed=" + closed
                + ")";
            // restore the user's progress mode after the auto-apply settled
            try {
                Thread.sleep(1000);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
            smtSettings.setModeOfProgressDialog(previousMode);
        }
        String finalReport = report;
        Platform.runLater(() -> {
            LOGGER.info("SMT verification: {}", finalReport);
            NotificationManagerF.getInstance()
                    .notify("SMT verification: " + finalReport,
                        finalReport.endsWith("PASS") ? Kind.INFO : Kind.ERROR);
        });
    }

    /**
     * loadingexit (P1): runs the loading/exit verification ({@code key.fx.verify.loadingexit}),
     * run after the demo load like the other proof-dependent verify hooks: (1) the recent-files
     * store round trip — an entry registered with loading options (profile ident, single-java
     * flag) survives the save/load cycle like Swing's recent-files entries, plus the
     * profile-ident resolution used when opening a recent file — both with a snapshot/restore so
     * the shared {@code recentFiles_v2.json} is not polluted; (2) the exit flow — the Confirm
     * Exit setting is switched off (snapshot/restore) and the window close button path is fired,
     * which must terminate the process with exit code 0.
     */
    private void runLoadingExitVerification() {
        String report;
        List<RecentFilesF.Entry> snapshot = recentFiles.getEntries();
        try {
            // the round trip uses a temp file so an existing demo entry is not reordered
            Path temp = Files.createTempFile("loadingexit-verify", ".key");
            Profile profile = ServiceLoader.load(DefaultProfileResolver.class).stream()
                    .map(resolver -> resolver.get().getDefaultProfile()).findFirst().orElse(null);
            if (profile == null) {
                report = "FAIL: no DefaultProfileResolver service";
            } else {
                recentFiles.add(temp.toAbsolutePath().toString(), profile.ident(), true, null);
                recentFiles.load();
                RecentFilesF.Entry entry = recentFiles.getEntries().isEmpty() ? null
                        : recentFiles.getEntries().getFirst();
                boolean stored = entry != null
                        && entry.path().equals(temp.toAbsolutePath().toString())
                        && profile.ident().equals(entry.profile()) && entry.singleJava();
                // profile resolution by ident (the recent-file open lookup, Swing
                // RecentFileMenu.java:403-406)
                boolean resolved = ServiceLoader.load(DefaultProfileResolver.class).stream()
                        .filter(resolver -> resolver.get().getProfileName().equals(profile.ident()))
                        .findFirst().isPresent();
                report = stored && resolved ? "PASS (store round trip + profile resolution)"
                        : "FAIL (stored=" + stored + ", resolved=" + resolved + ")";
                Files.deleteIfExists(temp);
            }
        } catch (IOException e) {
            report = "FAIL: " + e;
        }
        // restore the store and the Confirm Exit setting before anything else
        recentFiles.restore(snapshot);
        ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        boolean confirmExit = vs.confirmExit();
        vs.setConfirmExit(false);
        if (report.startsWith("PASS")) {
            LOGGER.info("loadingexit verification: {} — closing the window", report);
            // the window close button path (stage.setOnCloseRequest -> exitApplication ->
            // exitApplicationWithoutInteraction): the process must terminate with exit code 0
            stage.fireEvent(new WindowEvent(stage, WindowEvent.WINDOW_CLOSE_REQUEST));
        } else {
            vs.setConfirmExit(confirmExit);
            LOGGER.info("loadingexit verification: {}", report);
            NotificationManagerF.getInstance()
                    .notify("Loading/exit verification: " + report,
                        report.startsWith("PASS") ? Kind.INFO : Kind.ERROR);
        }
    }

    /**
     * termmenu: headless self test of the sequent context menu ({@code key.fx.verify.termmenu}),
     * run after the demo load like the other proof-dependent verify hooks: computes a
     * {@link PosInSequent} at a known character index of the current printing, builds the menu
     * with {@link SequentMenuModelF#build} + {@link SequentTermContextMenuF#build} and asserts
     * the fixed structural items on the rendered {@link ContextMenu}. Text report on stdout only
     * — no screenshots, no interaction. Skips gracefully when no goal or position is available.
     *
     * @param env the environment of the loaded proof
     */
    private void runTermMenuVerification(KeYEnvironment<DefaultUserInterfaceControl> env) {
        Goal goal = mediator.getSelectedGoal();
        PosInSequent pos = findTermMenuPos();
        if (goal == null || pos == null) {
            System.out.println("termmenu verify: SKIP - no goal/position (no printed sequent)");
            return;
        }
        List<SequentMenuModelF.Entry> entries =
            SequentMenuModelF.build(pos, mediator, env.getProofControl(), null, null);
        ContextMenu menu = SequentTermContextMenuF.build(entries,
            new SequentTermContextMenuF.MenuContext(mediator, env.getProofControl(), goal, pos,
                null, sequentView::printSequent));
        List<String> labels = new ArrayList<>();
        int[] enabled = { 0 };
        collectMenuLabels(menu.getItems(), labels, enabled);
        boolean hasFocus = labels.contains("Apply rules automatically here");
        boolean hasCopy = labels.contains("Copy to clipboard");
        boolean hasNoRules = labels.contains("No rules applicable.");
        boolean pass = menu.getItems().size() >= 4 && hasFocus && hasCopy
                && (hasNoRules || enabled[0] > 0);
        List<String> found = new ArrayList<>();
        found.add("focus_auto_mode");
        found.add("copy_clipboard");
        if (hasNoRules) {
            found.add("no_rules");
        }
        System.out.println("termmenu verify: " + (pass ? "OK" : "FAIL") + " - "
            + menu.getItems().size() + " items, found: " + String.join(", ", found));
    }

    /**
     * menu: MP8 — headless self test of the MP8a/MP8b term-menu wiring
     * ({@code key.fx.verify.termmenuwiring}), run after the demo load like the termmenu hook:
     * builds the term menu through the same seam as {@link #runTermMenuVerification} and
     * asserts (a) the {@code focus_auto_mode} item ("Apply rules automatically here") is ENABLED
     * and its action handler is non-null (Swing FocussedAutoModeUserAction, wired at
     * FocussedAutoModeUserAction.java:43), and (b) the {@code macro_menu} section ("Strategy
     * Macros", Swing ProofMacroMenu.java:81) exists and contains exactly the four macro names of
     * the Automation submenu ({@link #AUTOMATION_MACROS}, same order). The handlers are
     * deliberately NOT invoked — starting a real focused auto mode or running a macro headless
     * mid-regression is too heavy; enablement and handler presence is the assertion.
     */
    private void runTermMenuWiringVerification(KeYEnvironment<DefaultUserInterfaceControl> env) {
        Goal goal = mediator.getSelectedGoal();
        PosInSequent pos = findTermMenuPos();
        if (goal == null || pos == null) {
            System.out.println(
                "termmenu wiring verify: SKIP - no goal/position (no printed sequent)");
            return;
        }
        List<SequentMenuModelF.Entry> entries =
            SequentMenuModelF.build(pos, mediator, env.getProofControl(), null, null);
        ContextMenu menu = SequentTermContextMenuF.build(entries,
            new SequentTermContextMenuF.MenuContext(mediator, env.getProofControl(), goal, pos,
                null, sequentView::printSequent));
        MenuItem focusItem = null;
        Menu macroMenu = null;
        for (MenuItem item : menu.getItems()) {
            if ("Apply rules automatically here".equals(item.getText())) {
                focusItem = item;
            }
            if (item instanceof Menu m && "Strategy Macros".equals(m.getText())) {
                macroMenu = m;
            }
        }
        boolean focusOk = focusItem != null && !focusItem.isDisable()
                && focusItem.getOnAction() != null;
        List<String> macroNames = new ArrayList<>();
        if (macroMenu != null) {
            for (MenuItem item : macroMenu.getItems()) {
                String text = menuItemText(item);
                if (!text.isEmpty()) {
                    macroNames.add(text);
                }
            }
        }
        List<String> expected = new ArrayList<>();
        for (ProofMacro macro : AUTOMATION_MACROS) {
            expected.add(macro.getName());
        }
        boolean macroOk = macroNames.equals(expected);
        boolean pass = focusOk && macroOk;
        System.out.println("termmenu wiring verify: " + (pass ? "PASS" : "FAIL") + " - "
            + "focus_auto_mode[" + (focusItem == null ? "missing"
                    : (focusOk ? "enabled" : "disabled-or-no-handler"))
            + "] macro_menu["
            + macroNames + "]");
    }

    /**
     * extension: MP9.0 — headless self test of the FX extension SPI
     * ({@code key.fx.verify.extensions}), run after the demo load like the other
     * proof-dependent verify hooks. Asserts (a) the facade discovers exactly the three ported
     * built-in extensions, (b) the two status-line controls of the facade appear in the built
     * status bar, (c) the Heatmap menu is a separate menu of the built menu bar, (d) the
     * SettingsManagerF registry holds the Heatmap settings provider, and (e) the term-menu
     * extension section renders the disabled placeholder when <em>no position</em> is available
     * (the fallback of SequentTermContextMenuF; contributed items would be enabled only with a
     * position). One stdout report line; skips the term-menu sub-assertion gracefully when no
     * goal is loaded.
     *
     * @param env the environment of the loaded proof
     */
    private void runExtensionVerification(KeYEnvironment<DefaultUserInterfaceControl> env) {
        boolean pass = true;
        StringBuilder sb = new StringBuilder();

        int discovered = KeYGuiExtensionFacadeF.discoveredCount();
        sb.append("discovered=").append(discovered);
        // MP9.1-9.6: the six keyext FX modules register further providers, so the count is no
        // longer fixed at 3 — the assertion is the built-in trio's presence and a sane number
        List<String> classes = KeYGuiExtensionFacadeF.getExtensions().stream()
                .map(e -> e.getClass().getName()).toList();
        pass &= discovered >= 3
                && discovered == classes.size()
                && classes.contains("de.uka.ilkd.key.gui.fx.extension.contrib.HeatmapF")
                && classes.contains(
                    "de.uka.ilkd.key.gui.fx.extension.contrib.ParallelProverStatusIndicatorF")
                && classes.contains(
                    "de.uka.ilkd.key.gui.fx.extension.contrib.ProfileNameInStatusBarF");

        List<Control> statusControls = KeYGuiExtensionFacadeF.getStatusLineControls();
        sb.append(" statusControls=").append(statusControls.size());
        HBox statusBar = buildStatusBar();
        // the two built-in status-line controls are always contributed; the keyext ports may
        // add more, so the assertion is a membership check on the built status bar
        pass &= statusControls.size() >= 2
                && statusBar.getChildren().containsAll(statusControls);

        MenuBar menuBar = buildMenuBar();
        boolean heatmapMenu =
            menuBar.getMenus().stream().anyMatch(m -> "Heatmap".equals(m.getText()));
        sb.append(" heatmapMenu=").append(heatmapMenu);
        pass &= heatmapMenu;

        boolean heatmapSettings = SettingsManagerF.getInstance().getProviders().stream()
                .anyMatch(p -> "Heatmap".equals(p.getDescription()));
        sb.append(" heatmapSettings=").append(heatmapSettings);
        pass &= heatmapSettings;

        // drawer: MP10 — the extension left-panel tabs are west drawer items now; with only the
        // ported built-in extensions registered none contributes tabs, so the west drawer holds
        // exactly its five built-in panels (+ one item per contributed left-panel tab)
        int facadeTabs = KeYGuiExtensionFacadeF.getLeftPanelTabs(this, mediator).size();
        int westItems = westDrawer == null ? -1 : westDrawer.getItems().size();
        sb.append(" westDrawerItems=").append(westItems);
        pass &= westItems == 5 + facadeTabs;

        // term-menu extension section: with no position the disabled placeholder must render
        // without crashing (SequentTermContextMenuF.extensionSection)
        Goal goal = mediator.getSelectedGoal();
        String termMenuSection;
        if (goal == null) {
            termMenuSection = "skipped";
        } else {
            PosInSequent pos = findTermMenuPos();
            List<SequentMenuModelF.Entry> entries = pos == null
                    ? List.of(new SequentMenuModelF.NamedAction("extension", "Extensions", null,
                        null))
                    : SequentMenuModelF.build(pos, mediator, env.getProofControl(), null, null);
            ContextMenu menu = SequentTermContextMenuF.build(entries,
                new SequentTermContextMenuF.MenuContext(mediator, env.getProofControl(), goal,
                    null, null, sequentView::printSequent));
            MenuItem extensionItem = menu.getItems().stream()
                    .filter(it -> "Extensions".equals(it.getText())).findFirst().orElse(null);
            boolean disabledFallback = extensionItem != null && extensionItem.isDisable()
                    && extensionItem.getOnAction() == null;
            termMenuSection = disabledFallback ? "disabled-fallback" : "FAIL";
            pass &= disabledFallback;
        }
        sb.append(" termmenuExtension=").append(termMenuSection);

        String report = (pass ? "PASS" : "FAIL") + " - " + sb;
        System.out.println("Extension verification: " + report);
        LOGGER.info("Extension verification: {}", report);
    }

    /**
     * drawer: MP10 — headless self test of the drawered main window layout
     * ({@code key.fx.verify.drawerlayout}), run after the demo load like the other
     * proof-dependent verify hooks. Asserts the west/east/south {@link DrawerF} hosts with
     * their expected item sets — the five built-in west panels plus one item per contributed
     * extension left-panel tab (= MP9.1-9.6: exploration + slicing) — and default expansions
     * (Proof Tree + Goal List share the west split in button order), then exercises the same
     * drag-and-drop seams the handlers invoke on the live drawers: a cross-port transfer of the
     * Strategy panel west→east and back (owner re-keying) and a button reorder whose split
     * follows the new button order. One stdout report line; leaves the drawers in their
     * pre-test arrangement.
     *
     * @param env the environment of the loaded proof
     */
    private void runDrawerLayoutVerification(KeYEnvironment<DefaultUserInterfaceControl> env) {
        boolean pass = true;
        StringBuilder sb = new StringBuilder();
        DrawerF west = getWestDrawer();
        DrawerF east = getEastDrawer();
        DrawerF south = getSouthDrawer();
        if (west == null || east == null || south == null) {
            System.out.println("Drawer layout verification: FAIL - hosts=null");
            return;
        }
        // MP9.1-9.6: the keyext left-panel tabs (exploration, slicing) are also west items, so
        // the expected count mirrors runExtensionVerification: five built-ins + one per tab
        int expectedWest = 5 + KeYGuiExtensionFacadeF.getLeftPanelTabs(this, mediator).size();
        sb.append("west=").append(west.getItems().size()).append(" east=")
                .append(east.getItems().size()).append(" south=").append(south.getItems().size());
        pass &= west.getItems().size() == expectedWest && east.getItems().size() == 1
                && south.getItems().size() == 0;
        pass &= west.getDockingSide() == Side.LEFT && west.isMultiselect();
        pass &= east.getDockingSide() == Side.RIGHT && east.isMultiselect();
        pass &= south.getDockingSide() == Side.BOTTOM;

        // default expansions: Proof Tree + Goal List share the west split in button order
        ObservableList<Node> westContent = west.getContentArea().getChildren();
        sb.append(" expanded=").append(westContent.size());
        pass &= westContent.size() == 2 && westContent.get(0) == west.getItems().get(0)
                && westContent.get(1) == west.getItems().get(1);

        // cross-port transfer round trip: Strategy panel west->east, then east->west
        boolean movedEast = false;
        boolean movedBack = false;
        DrawerItemF strategy = west.getItems().size() > 4 ? west.getItems().get(4) : null;
        if (strategy != null && "Strategy".equals(strategy.getButton().getText())) {
            west.transferItem(strategy, east);
            movedEast = east.getItems().size() == 2 && east.getItems().contains(strategy)
                    && strategy.getDrawer() == east;
            east.transferItem(strategy, west);
            movedBack = west.getItems().size() == expectedWest && east.getItems().size() == 1
                    && strategy.getDrawer() == west && !east.getItems().contains(strategy);
        }
        sb.append(" transferRoundTrip=").append(movedEast && movedBack ? "PASS" : "FAIL");
        pass &= movedEast && movedBack;

        // button reorder: move the first west button behind the third; bar + split follow
        boolean reorderOk = false;
        if (west.getItems().size() > 2) {
            DrawerItemF first = west.getItems().get(0);
            west.moveItem(0, 2);
            reorderOk = west.getItems().get(2) == first
                    && west.getContentArea().getChildren().contains(first);
            west.moveItem(2, 0);
            reorderOk &= west.getItems().get(0) == first;
        }
        sb.append(" reorder=").append(reorderOk ? "PASS" : "FAIL");
        pass &= reorderOk;

        String report = (pass ? "PASS" : "FAIL") + " - " + sb;
        System.out.println("Drawer layout verification: " + report);
        LOGGER.info("Drawer layout verification: {}", report);
    }

    /**
     * menu: MP8 — visible text of a menu item, unwrapping label-backed {@code CustomMenuItem}s
     * (the macro items of the term menu carry their name in the wrapped label).
     */
    private static String menuItemText(MenuItem item) {
        String text = item.getText();
        if (text != null && !text.isEmpty()) {
            return text;
        }
        if (item instanceof CustomMenuItem custom && custom.getContent() instanceof Label label) {
            return label.getText();
        }
        return "";
    }

    /**
     * termmenu: the first {@link PosInSequent} of the current printing (the printed text may
     * start with whitespace or symbols that do not map to a position — the first indexed
     * character that resolves is used).
     */
    private PosInSequent findTermMenuPos() {
        String printed = sequentView.printedText();
        if (printed == null) {
            return null;
        }
        for (int i = 0; i < printed.length(); i++) {
            PosInSequent pos = sequentView.getSequentPosAt(i);
            if (pos != null) {
                return pos;
            }
        }
        return null;
    }

    /**
     * termmenu: collects the labels of a menu-item tree (sub-menus are flattened) and counts the
     * enabled, non-separator items.
     */
    private static void collectMenuLabels(List<MenuItem> items, List<String> labels,
            int[] enabled) {
        for (MenuItem item : items) {
            if (!(item instanceof SeparatorMenuItem)) {
                labels.add(item.getText());
                if (!item.isDisable()) {
                    enabled[0]++;
                }
            }
            if (item instanceof Menu menu) {
                collectMenuLabels(menu.getItems(), labels, enabled);
            }
        }
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
        // smalldialogs: F1 context help is handled by HelpFacadeF.installAccelerator(scene)
        // (registered in initialize), not here — a second handler would open the page twice.
    }

    /**
     * The UI's own auto mode listener: refreshes the views from the final state after an
     * <em>interactive</em> auto mode run (Swing {@code MainWindow.autoModeStopped}). The demo's
     * live run has its own listener which also runs the verification reports; the UI listener
     * skips the refresh in that case to avoid the duplicate work.
     */
    /**
     * inputfreeze (P1) — the blocking overlay of the auto mode freeze (Swing
     * {@code BlockingGlassPane} + {@code GlassPaneListener}, MainWindow.java:1620-1746): shown
     * by {@link #freezeExceptAutoModeButton()} for the duration of an auto mode run, it covers
     * the main area (workspace + drawers), blocks all mouse input, swallows key events targeted
     * inside it (except Escape, which reaches the global stop handler) and shows the wait
     * cursor. The top toolbar with the automation/stop controls and the status bar stay live.
     */
    private final Pane inputBlocker = new Pane();

    /**
     * inputfreeze (P1) — Swing {@code MainWindow.freezeExceptAutoModeButton} (MainWindow.java
     * :934): during auto mode all input except the stop controls is frozen. The FX overlay
     * covers the main area only — the menu bar, the toolbar (with the stop controls) and the
     * status bar stay interactive.
     * <p>
     * KNOWN-SIMPLIFIED: Swing's glass pane covered the whole content pane and re-delivered
     * events only to components marked {@code isAutoButton} (the automation/stop buttons and
     * the status-line abort button); the FX overlay instead covers only the views area, so the
     * menus stay clickable while frozen (their actions are disabled during auto mode anyway).
     */
    private void freezeExceptAutoModeButton() {
        inputBlocker.setVisible(true);
    }

    /** inputfreeze (P1) — Swing {@code MainWindow.unfreezeExceptAutoModeButton} (:944). */
    private void unfreezeExceptAutoModeButton() {
        inputBlocker.setVisible(false);
    }

    private final AutoModeListener autoModeUiListener = new AutoModeListener() {
        @Override
        public void autoModeStarted(ProofEvent e) {
            LOGGER.info("Auto mode started");
            FxUtil.runLater(this::freeze);
        }

        @Override
        public void autoModeStopped(ProofEvent e) {
            // inputfreeze (P1): unfreeze before the demo-live early return — every stop must
            // undo the freeze
            FxUtil.runLater(this::unfreeze);
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

        /** inputfreeze (P1): shows the blocking overlay (Swing freezeExceptAutoModeButton). */
        private void freeze() {
            freezeExceptAutoModeButton();
        }

        /** inputfreeze (P1): hides the blocking overlay (Swing unfreezeExceptAutoModeButton). */
        private void unfreeze() {
            unfreezeExceptAutoModeButton();
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
        // drawer: MP10 — the Loaded Proofs / Goal List / Proof Tree / Info / Strategy panels
        // moved out of the docking area into the west drawer (buildDrawerHosts), the Source view
        // into the east drawer; the docking centre now only hosts the sequent (its dock actions,
        // layout slots and shutdown persistence keep working). The left/right dock-layout
        // registrations are gone, so DockLayoutStore was bumped to version 2: older persisted
        // layouts referencing the removed dockables are discarded (they were the pre-MP10
        // arrangement) and the workspace falls back to the factory default — the sequent only.
        dockables.put(ID_SEQUENT, new SimpleDockable(ID_SEQUENT, "Sequent", sequentView));
    }

    /**
     * drawer: MP10 — builds the west/east/south drawer hosts of the main window (Java port of
     * the TornadoFX {@code Drawer}). The panels of the Swing left tab area / right dock become
     * drawer items: a toggle button per panel in the drawer's button bar; expanding a button
     * shows the panel in the split next to the bar, always in the order of the buttons. The
     * drawers are multiselect (the tornadofx "Multiselect" mode) so Proof Tree and Goal List
     * share the west split; the per-item header distinguishes them there.
     * <p>
     * Drag and drop (added on top of the original implementation) turns this into a docking
     * UI: dragging a button onto another drawer moves the panel to that port (e.g. the Strategy
     * panel from west to east), dragging within a bar reorders the panels in the split. The
     * south drawer starts empty — it is the drop port for panels dragged there and the future
     * home of a log console; the log view stays a separate window ({@link #showLogView()}),
     * matching the Swing status-line behaviour.
     */
    private void buildDrawerHosts() {
        westDrawer = new DrawerF(Side.LEFT, true);
        westDrawer.item("Proof Tree", proofTreeView, true);
        westDrawer.item("Goal List", goalListView, true);
        westDrawer.item("Loaded Proofs", loadedProofs);
        westDrawer.item("Info", infoView);
        westDrawer.item("Strategy", strategyView);
        // extension: MP10 — the extension left-panel tabs become west drawer items (Swing
        // KeYGuiExtension.LeftPanel returns tabs for the left JTabbedPane,
        // KeYGuiExtension.java:127-143): a button per tab in the west bar toggles the panel,
        // drag and drop can move it to another port; without LeftPanelF providers this appends
        // nothing.
        for (Tab tab : KeYGuiExtensionFacadeF.getLeftPanelTabs(this, mediator)) {
            westDrawer.item(tab.getText(), tab.getContent());
        }
        eastDrawer = new DrawerF(Side.RIGHT, true);
        eastDrawer.item("Source", buildSourceViewContent());
        southDrawer = new DrawerF(Side.BOTTOM, true);
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
        // drawer: MP10 — only the sequent remains dockable; the west/east/south panels are
        // drawer items (buildDrawerHosts) and the extension left panels are west drawer items
        List<DockWorkspace.Default> defaults = new ArrayList<>();
        defaults.add(new DockWorkspace.Default(DockLocation.MAIN, requireDockable(ID_SEQUENT)));
        return defaults;
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
        // extension: MP9.0 — a third toolbar holds the controls contributed by the FX
        // extensions (Swing MainWindow.appendToolbar /
        // KeYGuiExtensionFacade.createToolbars, KeYGuiExtensionFacade.java:217-221: each
        // extension toolbar is embedded next to the built-in file/proof toolbars); shown only
        // when an extension contributes controls.
        List<Control> extensionToolbarControls =
            KeYGuiExtensionFacadeF.getToolbarControls(this, mediator);
        if (!extensionToolbarControls.isEmpty()) {
            ToolBar extensionToolBar = new ToolBar();
            extensionToolBar.getStyleClass().add("key-extension-tool-bar");
            extensionToolBar.getItems().addAll(extensionToolbarControls);
            toolBarArea.getChildren().add(extensionToolBar);
        }
        toolBarArea.getStyleClass().add("key-toolbar-area");
        top.getChildren().addAll(menuBar, toolBarArea);
        return top;
    }

    private MenuBar buildMenuBar() {
        MenuBar menuBar = new MenuBar();
        menuBar.getMenus().addAll(buildFileMenu(), buildViewMenu(), buildProofMenu(),
            buildOptionsMenu(), buildAboutMenu());
        // extension: MP9.0 — the extension-contributed menus are appended after the About menu
        // as NEW separate menu-bar menus (Swing MainWindow.createMenuBar :983 calls
        // KeYGuiExtensionFacade.addExtensionsToMainMenu after the built-in menus,
        // KeYGuiExtensionFacade.java:81-89; the Swing original groups the extension actions
        // into one "Extensions" JMenu, the FX SPI contributes whole Menu objects — the
        // grouping decision stays with the extension). The five built-in menus' item sets are
        // untouched: key.fx.verify.menuparity keeps asserting 16/24/12/7/5.
        List<javafx.scene.control.Menu> extensionMenus =
            KeYGuiExtensionFacadeF.getMenus(this, mediator);
        if (!extensionMenus.isEmpty()) {
            menuBar.getMenus().addAll(extensionMenus);
        }
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
        // menu: MP5 — edit the most recently opened file in the default external editor (Swing
        // EditMostRecentFileAction, placed right after Reload like MainWindow.createFileMenu
        // :997-998). Swing enables the action as long as a recent file exists (binding to the
        // most-recent-file state) and opens the file with Desktop.open/EditFileActionHandler; the
        // FX port opens the file's file:// URI through the HelpFacadeF browser seam (host
        // services, like the About browser actions).
        MenuItem editLastOpenedFile =
            menuItem("Edit Last Opened File",
                "de.uka.ilkd.key.gui.actions.EditMostRecentFileAction",
                IconFactoryF.Key.EDIT, this::editLastOpenedFile);
        // menu: MP5 — bound to the RecentFilesF "has a recent file" property (the Swing original
        // re-checks the list when the menu is shown); disabled during auto mode like the other
        // file actions.
        editLastOpenedFile.disableProperty().bind(mediator.autoModeRunningProperty()
                .or(recentFiles.hasRecentFileProperty().not()));
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
        // menu: MP5 — load user-defined taclets into the current proof (Swing
        // LemmaGenerationAction.ProveAndAddTaclets, Mode.LOAD; after Proof Management like
        // MainWindow.createFileMenu :1019-1021). A proof is required (Swing proofIsRequired()).
        MenuItem loadUserDefinedTaclets =
            menuItem("Load User Defined Taclets…",
                "de.uka.ilkd.key.gui.actions.LemmaGenerationAction$ProveAndAddTaclets",
                this::loadUserDefinedTaclets);
        loadUserDefinedTaclets.disableProperty().bind(mediator.autoModeRunningProperty()
                .or(proofLoaded.not()));
        file.getItems().addAll(
            openExample,
            openFile,
            reload,
            editLastOpenedFile,
            new SeparatorMenuItem(),
            proofManagement,
            loadUserDefinedTaclets,
            buildProveSubmenu(),
            saveFile,
            saveBundle,
            quickSave,
            quickLoad,
            new SeparatorMenuItem(),
            recentFilesMenu,
            new SeparatorMenuItem(),
            menuItem("Exit", "de.uka.ilkd.key.gui.actions.ExitMainAction",
                IconFactoryF.Key.QUIT, this::exitApplication));
        return file;
    }

    /**
     * menu: MP5 — the File&gt;Prove submenu (Swing {@code MainWindow.createFileMenu} :1022-1031:
     * {@code Load User Defined Taclets for Proving} = {@code LemmaGenerationAction
     * .ProveUserDefinedTaclets}, {@code Load KeY Taclets} = {@code LemmaGenerationAction
     * .ProveKeYTaclets}, {@code Lemma Generation (Batch Mode)} = {@code
     * LemmaGenerationBatchModeAction} info dialog, and the {@code Run All Proofs} QA action
     * behind the {@link FeatureSettings} flag {@code BULK_UI_TEST}). The Prove entries need no
     * proof (Swing {@code proofIsRequired() == false}) and are only disabled during auto mode.
     */
    private Menu buildProveSubmenu() {
        Menu prove = new Menu("Prove");
        MenuItem proveUserDefined = menuItem("Load User Defined Taclets for Proving",
            "de.uka.ilkd.key.gui.actions.LemmaGenerationAction$ProveUserDefinedTaclets",
            this::proveUserDefinedTaclets);
        proveUserDefined.disableProperty().bind(mediator.autoModeRunningProperty());
        MenuItem proveKeYTaclets = menuItem("Load KeY Taclets",
            "de.uka.ilkd.key.gui.actions.LemmaGenerationAction$ProveKeYTaclets",
            this::proveKeYTaclets);
        proveKeYTaclets.disableProperty().bind(mediator.autoModeRunningProperty());
        MenuItem lemmaBatchMode = menuItem("Lemma Generation (Batch Mode)",
            "de.uka.ilkd.key.gui.actions.LemmaGenerationBatchModeAction",
            this::showLemmaGenerationBatchMode);
        lemmaBatchMode.disableProperty().bind(mediator.autoModeRunningProperty());
        prove.getItems().addAll(proveUserDefined, proveKeYTaclets, lemmaBatchMode);

        // menu: MP5 — "Run All Proofs" behind the BULK_UI_TEST feature flag, mirroring the
        // Swing registration (FeatureSettings.onAndActivate(FEATURE_BULK_UI_TEST,
        // showRAPAction), MainWindow.java:1023-1027). The item's visibility follows the flag;
        // the listener is registered at most once — the parity self test rebuilds the menu bar,
        // which would otherwise stack duplicate listeners on the shared FeatureSettings.
        MenuItem runAllProofs = menuItem("Run All Proofs",
            "de.uka.ilkd.key.gui.actions.RunAllProofsAction", this::runAllProofs);
        runAllProofs.setVisible(FeatureSettings.isFeatureActivated(FEATURE_BULK_UI_TEST));
        if (!bulkUiTestListenerRegistered) {
            bulkUiTestListenerRegistered = true;
            FeatureSettings.onAndActivate(FEATURE_BULK_UI_TEST, runAllProofs::setVisible);
        }
        prove.getItems().add(runAllProofs);
        return prove;
    }

    private Menu buildViewMenu() {
        Menu view = new Menu("View");
        // menu: MP3a — Pretty Print toggle (Swing PrettyPrintToggleAction,
        // PrettyPrintToggleAction.java:45-59): updateSelectedState mirrors the settings into the
        // NotationInfo static and the selected state; actionPerformed sets the static BEFORE the
        // ViewSettings are modified, because the UI reacts on the settings change event (the
        // printers consult the static at construction). The re-render mirrors
        // MainWindow.makePrettyView (MainWindow.java:954-959).
        ViewSettings viewSettings = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        CheckMenuItem prettyPrint = new CheckMenuItem("Pretty Print");
        NotationInfo.DEFAULT_PRETTY_SYNTAX = viewSettings.isUsePretty();
        prettyPrint.setSelected(viewSettings.isUsePretty());
        prettyPrint.setOnAction(e -> {
            boolean selected = prettyPrint.isSelected();
            // Swing: "Needs to be executed before the ViewSettings are modified, because the UI
            // will react on the settings change event!" (PrettyPrintToggleAction.java:55-57)
            NotationInfo.DEFAULT_PRETTY_SYNTAX = selected;
            viewSettings.setUsePretty(selected);
            refreshPrettyViews();
        });
        // menu: MP3a — Unicode toggle (Swing UnicodeToggleAction, UnicodeToggleAction.java:47-69):
        // only meaningful in combination with pretty printing (updateSelectedState:
        // setEnabled(usePretty), setSelected(useUnicode && usePretty)); the disable binding
        // replaces Swing's setEnabled(usePretty).
        CheckMenuItem unicode = new CheckMenuItem("Unicode Symbols");
        unicode.setSelected(viewSettings.isUseUnicode() && viewSettings.isUsePretty());
        unicode.setDisable(!viewSettings.isUsePretty());
        unicode.disableProperty().bind(prettyPrint.selectedProperty().not());
        unicode.setOnAction(e -> {
            boolean selected = unicode.isSelected();
            boolean pretty = viewSettings.isUsePretty();
            // before the ViewSettings are modified, like the Swing original
            // (UnicodeToggleAction.java:63)
            NotationInfo.DEFAULT_UNICODE_ENABLED = selected && pretty;
            viewSettings.setUseUnicode(selected);
            refreshPrettyViews();
        });
        CheckMenuItem syntaxHighlighting = new CheckMenuItem("Syntax Highlighting");
        syntaxHighlighting.setSelected(sequentView.isSyntaxHighlightingEnabled());
        syntaxHighlighting.setOnAction(
            e -> sequentView.setSyntaxHighlightingEnabled(syntaxHighlighting.isSelected()));

        // menu: MP3a — tooltip toggles (Swing ToggleSequentViewTooltipAction /
        // ToggleSourceViewTooltipAction / ToggleProofTreeTooltipAction, MainWindow.createViewMenu
        // :1042-1044): each persists the shared ViewSettings flag like the Swing actionPerformed
        // implementations. The sequent view consults isShowSequentViewTooltips() in its tooltip
        // code (SequentViewF.getTooltipText, SequentViewF.java:824-835), so the toggle needs no
        // re-render; the proof tree re-creates its cell tooltips on refresh().
        CheckMenuItem showSequentViewTooltips = new CheckMenuItem("Show Tooltips in Sequent View");
        showSequentViewTooltips.setSelected(viewSettings.isShowSequentViewTooltips());
        showSequentViewTooltips.setOnAction(
            e -> viewSettings.setShowSequentViewTooltips(showSequentViewTooltips.isSelected()));
        CheckMenuItem showSourceViewTooltips = new CheckMenuItem("Show Tooltips in Source View");
        showSourceViewTooltips.setSelected(viewSettings.isShowSourceViewTooltips());
        // menu: MP3a — no source view in the FX UI: the toggle only persists the flag (Swing
        // ToggleSourceViewTooltipAction, ToggleSourceViewTooltipAction.java:58-62)
        showSourceViewTooltips.setOnAction(
            e -> viewSettings.setShowSourceViewTooltips(showSourceViewTooltips.isSelected()));
        CheckMenuItem showProofTreeTooltips = new CheckMenuItem("Show Tooltips in Proof Tree");
        showProofTreeTooltips.setSelected(viewSettings.isShowProofTreeTooltips());
        showProofTreeTooltips.setOnAction(e -> {
            viewSettings.setShowProofTreeTooltips(showProofTreeTooltips.isSelected());
            // re-render the cells so the per-cell tooltip appears/disappears immediately (the
            // cell tooltip consults the flag, see ProofTreeViewF.ProofTreeCell.updateItem)
            proofTreeView.refresh();
        });

        // menu: MP3a — the Ctrl+P / Ctrl+U accelerators of the Swing KeyStrokeManager
        // (KeyStrokeManagerF.registerDefaults) apply to the check items like to the plain
        // menuItem() factory items.
        KeyStrokeManagerF shortcuts = KeyStrokeManagerF.getInstance();
        shortcuts.binding("de.uka.ilkd.key.gui.actions.PrettyPrintToggleAction")
                .ifPresent(prettyPrint::setAccelerator);
        shortcuts.register(prettyPrint, "de.uka.ilkd.key.gui.actions.PrettyPrintToggleAction");
        shortcuts.binding("de.uka.ilkd.key.gui.actions.UnicodeToggleAction")
                .ifPresent(unicode::setAccelerator);
        shortcuts.register(unicode, "de.uka.ilkd.key.gui.actions.UnicodeToggleAction");

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
        // P3b/B18: Swing order + labels of the Font Size submenu
        // (MainWindow.createViewMenu :1048-1051: first DecreaseFontSizeAction = "Smaller" with the
        // minus icon, then IncreaseFontSizeAction = "Larger"; DecreaseFontSizeAction.java:30 /
        // IncreaseFontSizeAction.java:30 set NAME to "Smaller"/"Larger", the menus show the minus
        // icon for "Smaller" and the plus icon for "Larger").
        fontSize.getItems().addAll(
            menuItem("Smaller", "de.uka.ilkd.key.gui.actions.DecreaseFontSizeAction",
                IconFactoryF.Key.MINUS, () -> changeFontSize(-1)),
            menuItem("Larger", "de.uka.ilkd.key.gui.actions.IncreaseFontSizeAction",
                IconFactoryF.Key.PLUS, () -> changeFontSize(1)));

        // menu: MP3a — ToolTip Options right after Font Size, before the diff frame, like Swing
        // MainWindow.createViewMenu :1053 (ToolTipOptionsAction → ViewSelector,
        // ToolTipOptionsAction.java:26 / ViewSelector.java:26-27).
        MenuItem toolTipOptions = menuItem("ToolTip Options…",
            "de.uka.ilkd.key.gui.actions.ToolTipOptionsAction", this::showToolTipOptions);

        // smalldialogs: the soundiness report (Swing ShowSoundinessAction, contributed to
        // the proof-list context menu by SoundinessExtension). The FX proof-list dockable
        // does not exist yet, so the action lives in the View menu; Swing
        // enableWhenProofLoaded + the general auto-mode lock carry over. Created as a
        // named item so the enablement binding below stays correct after the lemmaorigin
        // addAll runs (the index-from-end trick of the standalone port no longer applies).
        javafx.scene.control.MenuItem soundinessItem = menuItem("Show Soundiness Report",
            "de.uka.ilkd.key.gui.actions.ShowSoundinessAction", this::showSoundinessReport);

        // menu: MP3b — end of the View menu, mirroring Swing MainWindow.createViewMenu
        // :1057-1064: separator, Select Goal submenu (createSelectionMenu :1069-1074, the
        // GoalSelectAboveAction / GoalSelectBelowAction call
        // mainWindow.getProofTreeView().selectAbove()/selectBelow(),
        // GoalSelectAboveAction.java:31-33), separator, Back/Forward over the SelectionHistory
        // controller (SelectionBackAction/SelectionForwardAction, SelectionHistory.java), and a
        // trailing separator. The Ctrl+K / Ctrl+J / Ctrl+Alt+Left / Ctrl+Alt+Right accelerators
        // arrive via the actionIds from KeyStrokeManagerF.registerDefaults (:122-123, :134-135).
        // The Select Goal items are proof-gated (Swing MainWindowAction enableWhenProofLoaded);
        // Back/Forward are enabled purely by the history like the Swing actions.
        Menu selectGoal = new Menu("Select Goal");
        MenuItem goalSelectAbove = menuItem("Select Goal Above",
            "de.uka.ilkd.key.gui.actions.GoalSelectAboveAction", this::selectGoalAbove);
        goalSelectAbove.disableProperty().bind(proofLoaded.not());
        MenuItem goalSelectBelow = menuItem("Select Goal Below",
            "de.uka.ilkd.key.gui.actions.GoalSelectBelowAction", this::selectGoalBelow);
        goalSelectBelow.disableProperty().bind(proofLoaded.not());
        selectGoal.getItems().addAll(goalSelectAbove, goalSelectBelow);
        MenuItem selectionBack = menuItem("Back",
            "de.uka.ilkd.key.gui.actions.SelectionBackAction", IconFactoryF.Key.PREVIOUS,
            selectionHistory::navigateBack);
        selectionBack.disableProperty().bind(selectionHistory.canGoBackProperty().not());
        MenuItem selectionForward = menuItem("Forward",
            "de.uka.ilkd.key.gui.actions.SelectionForwardAction", IconFactoryF.Key.NEXT,
            selectionHistory::navigateForward);
        selectionForward.disableProperty().bind(selectionHistory.canGoForwardProperty().not());

        view.getItems().addAll(prettyPrint, unicode, syntaxHighlighting);
        // lemmaorigin: begin — term labels + origin tracking view controls (Swing TermLabelMenu /
        // HidePackagePrefixToggleAction / OriginTermLabelsExt MainMenu items)
        // menu: MP3a — moved to the Swing position right after Syntax Highlighting
        // (MainWindow.createViewMenu :1040-1041 appends termLabelMenu and hidePackagePrefix before
        // the tooltip toggles), so the View menu follows the Swing order
        view.getItems().addAll(OriginLabelsF.install(this));
        // lemmaorigin: end
        view.getItems().addAll(showSequentViewTooltips, showSourceViewTooltips,
            showProofTreeTooltips,
            new SeparatorMenuItem(),
            themeMenu, fontSize, toolTipOptions, new SeparatorMenuItem(),
            menuItem("Visual Node Diff", "de.uka.ilkd.key.gui.proofdiff.ProofDiffFrame$Action",
                this::showProofDiffFrame),
            new SeparatorMenuItem(),
            // docking: named layout slots (Swing DockingLayout, menu path View > Layout)
            dockingLayout.layoutMenu(),
            // seam: the Swing LogView is opened by a status-line extension button
            // (ShowLogAction; no FX extension SPI yet), so the FX entry point is a View menu
            // item (LogViewF.showInstance)
            menuItem("Log View", "de.uka.ilkd.key.gui.actions.LogViewAction",
                this::showLogView),
            soundinessItem,
            new SeparatorMenuItem(), selectGoal, new SeparatorMenuItem(),
            selectionBack, selectionForward, new SeparatorMenuItem());
        soundinessItem.disableProperty()
                .bind(mediator.autoModeRunningProperty().or(proofLoaded.not()));
        return view;
    }

    /**
     * menu: MP3b — selects the next open goal above the current tree selection (Swing
     * {@code GoalSelectAboveAction.actionPerformed} →
     * {@code mainWindow.getProofTreeView().selectAbove()}, GoalSelectAboveAction.java:25-34).
     */
    private void selectGoalAbove() {
        proofTreeView.selectAbove();
    }

    /**
     * menu: MP3b — selects the next open goal below the current tree selection (Swing
     * {@code GoalSelectBelowAction.actionPerformed} →
     * {@code mainWindow.getProofTreeView().selectBelow()}, GoalSelectBelowAction.java:25-34).
     */
    private void selectGoalBelow() {
        proofTreeView.selectBelow();
    }

    /**
     * menu: MP3a — re-renders the sequent and goal list views after the Pretty Print / Unicode
     * Symbols toggles (Swing {@code MainWindow.makePrettyView}, MainWindow.java:954-959: refresh
     * the mediator's shared NotationInfo against the services and re-display the sequent). The FX
     * views build their own NotationInfo per print (they do not use the mediator's shared
     * instance yet) and expose the re-render as {@code refreshPrettyView} hooks; the goal list
     * prints terms too, so it is refreshed the same way.
     */
    private void refreshPrettyViews() {
        sequentView.refreshPrettyView();
        goalListView.refreshPrettyView();
    }

    /**
     * menu: MP3a — opens the tooltip options dialog (Swing {@code ToolTipOptionsAction},
     * ToolTipOptionsAction.java:26, constructs the {@code ViewSelector}). The dialog edits the
     * shared {@code ViewSettings} directly.
     */
    private void showToolTipOptions() {
        ToolTipOptionsDialogF.show(stage);
    }

    /**
     * seam: opens the log view window (Swing {@code ShowLogAction} →
     * {@code LogView.showInstance}, {@code LogView.java:88-126}).
     */
    private void showLogView() {
        LogViewF.showInstance(getStage());
    }

    /**
     * menu: MP2/MP7 — the proof macros of the Automation submenu (Swing
     * {@code MainWindow.createAutomationActions}, MainWindow.java:814-827, in the same order:
     * DefaultAutoMacro, FullAutoPilotProofMacro, AutoPilotPrepareProofMacro, ScriptAwareMacro).
     * Shared with the sequent-view right-click macro popup (MP7; Swing {@code
     * ProofMacroMenu.REGISTERED_MACROS} is the ServiceLoader superset, ProofMacroMenu.java:60-61
     * — the FX popup mirrors the app's own Automation submenu instead, see
     * SequentViewF#buildMacroPopup).
     */
    public static final List<ProofMacro> AUTOMATION_MACROS =
        List.of(new DefaultAutoMacro(), new FullAutoPilotProofMacro(),
            new AutoPilotPrepareProofMacro(), new ScriptAwareMacro());

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
        automation.getItems().add(startAuto);
        automation.getItems().add(stopAuto);
        // menu: MP2 — after Start/Stop Automatic Proof the Automation submenu mirrors the four
        // proof-macro entries of Swing MainWindow.createAutomationActions (MainWindow.java:814-827,
        // MacroAutomationAction.java:40-45), same order, item text = macro.getName(). The Swing
        // icons (IconFactory.automationWithOverlay(TOOLBAR_ICON_SIZE, "A"|"S"|"P"|"J"),
        // MainWindow.java:817-827) have no FX counterpart in IconFactoryF.Key, so the items pass
        // null.
        // The actionId is the FQN binding key of KeyStrokeManagerF.registerDefaults
        // (KeyStrokeManagerF.java:83-84), so the existing Ctrl+V / Ctrl+D accelerators of
        // FullAutoPilotProofMacro / AutoPilotPrepareProofMacro are wired automatically (that was
        // the point of the key binding); DefaultAutoMacro and ScriptAwareMacro have no default
        // binding but are still registered with the manager for settings-driven rebinding.
        // Enablement binds to proofLoaded only — deliberately NO auto-mode lock: Swing keeps the
        // macro actions enabled while auto mode runs so a click stops the automation
        // (MacroAutomationAction.actionPerformed, MacroAutomationAction.java:48-61).
        // menu: MP7 — the items are built from the shared {@link #AUTOMATION_MACROS} list so the
        // right-click macro popup of the sequent view (SequentViewF#buildMacroPopup) offers the
        // very same macros.
        for (ProofMacro macro : AUTOMATION_MACROS) {
            MenuItem autoItem = menuItem(macro.getName(),
                "de.uka.ilkd.key.macros." + macro.getClass().getSimpleName(), null,
                () -> runMacro(macro));
            autoItem.disableProperty().bind(proofLoaded.not());
            automation.getItems().add(autoItem);
        }
        // menu: MP1 — the entries after Prune Proof mirror Swing MainWindow.createProofMenu
        // (MainWindow.java:1082-1142) with selected == null in the same order: Abandon Proof,
        // separator, the search group (Search in Proof Tree/Sequent + Next/Previous + the
        // Search Mode submenu), separator, then Show Used Contracts / Show All Active Settings /
        // Show Proof Statistics / Show Known Types. The search group and the
        // statistics/settings group are proof-gated via proofLoaded (Swing
        // enableWhenProofLoaded on each action); Abandon Proof additionally carries the
        // auto-mode lock (Swing AbandonTaskAction is enabled whenever a proof is loaded, but the
        // removal of a running proof stops auto mode first — keep the lock like the other
        // interaction actions).
        // menu: Abandon Proof — Swing AbandonTaskAction (AbandonTaskAction.java:13-46), reused
        // actionId so the Ctrl+W accelerator from KeyStrokeManagerF (defineDefault
        // AbandonTaskAction
        // = modifier()+W, KeyStrokeManagerF.java:117) is bound; enablement mirrored from
        // enableWhenProofLoaded + the auto-mode lock.
        MenuItem abandonProof = menuItem("Abandon Proof",
            "de.uka.ilkd.key.gui.actions.AbandonTaskAction",
            IconFactoryF.Key.CLOSE, this::abandonProof);
        abandonProof.disableProperty()
                .bind(mediator.autoModeRunningProperty().or(proofLoaded.not()));
        // menu: search group — Swing SearchInProofTreeAction / SearchInSequentAction /
        // SearchNextAction / SearchPreviousAction (MainWindow.java:1121-1124) and the
        // SearchModeChangeAction entries of the "Search Mode" submenu (:1125-1131). All bound
        // only to proofLoaded (matches the FX read-only-action style: no auto-mode lock).
        MenuItem searchInTree = menuItem("Search in Proof Tree",
            "de.uka.ilkd.key.gui.actions.SearchInProofTreeAction",
            IconFactoryF.Key.PROOF_TREE, proofTreeView::showSearchBar);
        searchInTree.disableProperty().bind(proofLoaded.not());
        MenuItem searchInSequent = menuItem("Search in Sequent",
            "de.uka.ilkd.key.gui.actions.SearchInSequentAction",
            IconFactoryF.Key.SEARCH, sequentView::showSearchBar);
        searchInSequent.disableProperty().bind(proofLoaded.not());
        MenuItem searchNext = menuItem("Search Next",
            "de.uka.ilkd.key.gui.actions.SearchNextAction",
            IconFactoryF.Key.NEXT, sequentView::searchNext);
        searchNext.disableProperty().bind(proofLoaded.not());
        MenuItem searchPrevious = menuItem("Search Previous",
            "de.uka.ilkd.key.gui.actions.SearchPreviousAction",
            IconFactoryF.Key.PREVIOUS, sequentView::searchPrevious);
        searchPrevious.disableProperty().bind(proofLoaded.not());
        Menu searchMode = new Menu("Search Mode");
        for (SequentViewF.SearchMode mode : SequentViewF.SearchMode.values()) {
            MenuItem modeItem = menuItem(mode.getDisplayName(),
                () -> sequentView.setSearchMode(mode));
            modeItem.disableProperty().bind(proofLoaded.not());
            searchMode.getItems().add(modeItem);
        }
        // menu: statistics/settings group — Swing ShowUsedContractsAction (:1134,
        // ProofManagementDialog with the selected proof preselected = openProofManagement()),
        // ShowActiveSettingsAction (:1138, ActiveSettingsDialogF), ShowProofStatistics (:1139,
        // ProofStatisticsDialogF) and ShowKnownTypesAction (:1140, KnownTypesDialogF). All
        // proof-gated (Swing enableWhenProofLoaded).
        MenuItem usedContracts = menuItem("Show Used Contracts",
            "de.uka.ilkd.key.gui.actions.ShowUsedContractsAction",
            this::openProofManagement);
        usedContracts.disableProperty().bind(proofLoaded.not());
        MenuItem activeSettings = menuItem("Show All Active Settings",
            "de.uka.ilkd.key.gui.actions.ShowActiveSettingsAction",
            IconFactoryF.Key.CONFIGURE, this::showActiveSettings);
        activeSettings.disableProperty().bind(proofLoaded.not());
        MenuItem proofStatistics = menuItem("Show Proof Statistics",
            "de.uka.ilkd.key.gui.actions.ShowProofStatistics",
            IconFactoryF.Key.STATISTICS, this::showProofStatistics);
        proofStatistics.disableProperty().bind(proofLoaded.not());
        MenuItem knownTypes = menuItem("Show Known Types",
            "de.uka.ilkd.key.gui.actions.ShowKnownTypesAction",
            this::showKnownTypes);
        knownTypes.disableProperty().bind(proofLoaded.not());
        proof.getItems().addAll(automation, new SeparatorMenuItem(),
            menuItem("Goal Back", "de.uka.ilkd.key.gui.actions.GoalBackAction",
                IconFactoryF.Key.GOAL_BACK, mediator::goalBack),
            menuItem("Prune Proof", "de.uka.ilkd.key.gui.actions.PruneProofAction",
                IconFactoryF.Key.PRUNE, mediator::pruneProof),
            abandonProof, new SeparatorMenuItem(),
            searchInTree, searchInSequent, searchNext, searchPrevious, searchMode,
            new SeparatorMenuItem(),
            usedContracts, activeSettings, proofStatistics, knownTypes);
        return proof;
    }

    // ------------------------------------------------------------------
    // proof menu actions (menu: MP1 — Swing MainWindow.createProofMenu :1082-1142)
    // ------------------------------------------------------------------

    /**
     * menu: MP2 — runs a proof macro on the selected node (Swing
     * {@code MacroAutomationAction.actionPerformed}, MacroAutomationAction.java:48-61): while auto
     * mode is running the click only stops it (Swing {@code proofControl.stopAutoMode()}, where
     * {@code proofControl = mediator.getUI().getProofControl()}); otherwise the macro runs on the
     * selected node ({@code new ProofMacroUserAction(mediator, macro, null).actionPerformed(e)}).
     * The macro-finished notifications are produced by {@link WindowUserInterfaceControlF}
     * (:380-398), which already reacts to the macro-sourced {@code ProofEvent}s.
     */
    private void runMacro(ProofMacro macro) {
        if (mediator.isInAutoMode()) {
            mediator.stopAutoMode(); // Swing: proofControl.stopAutoMode()
        } else if (lastEnvironment != null) {
            lastEnvironment.getProofControl().runMacro(mediator.getSelectedNode(), macro, null);
        }
    }

    /**
     * menu: abandons the selected proof (Swing {@code AbandonTaskAction.actionPerformed},
     * AbandonTaskAction.java:33-46): asks for confirmation first (Swing
     * {@code confirmTaskRemoval("Are you sure?")}, a YES/NO dialog titled "Abandon Proof",
     * WindowUserInterfaceControl.java:341-345), stops auto mode if the proof is being proved
     * automatically, disposes the proof and resets the UI to its "no proof" state.
     */
    private void abandonProof() {
        Proof proof = selectionModel.getSelectedProof();
        if (proof == null) {
            return; // the item is disabled without a proof (Swing enableWhenProofLoaded)
        }
        Alert alert = new Alert(Alert.AlertType.CONFIRMATION, "Are you sure?");
        alert.setTitle("Abandon Proof");
        alert.setHeaderText(null);
        alert.initOwner(stage);
        ExampleChooserF.themeDialogPane(alert);
        Optional<ButtonType> result = alert.showAndWait();
        if (result.isEmpty() || result.get() != ButtonType.OK) {
            return; // Swing: confirmTaskRemoval returns false on No/close
        }
        // menu: stop auto mode through the window's proof control if a run is active (Swing
        // getMediator().getUI().getProofControl().stopAutoMode()); lastEnvironment is the loaded
        // env of the selection (like the other proof-dependent flows, see :603-622)
        if (mediator.isInAutoMode() && lastEnvironment != null) {
            lastEnvironment.getProofControl().stopAutoMode();
        }
        // menu: unregister from the multi-proof state (Swing TaskTree.removeProof on abandon,
        // TaskTree.java:241-267; ProofManagerF.removeProof was provided for exactly this caller)
        proofManager.removeProof(proof);
        proof.dispose();
        // menu: reset the UI to the "no proof" state — the selection model supports a null
        // selection (KeYSelectionModel.setSelectedProof(null) nulls the selection and fires
        // selectedProofChanged, KeYSelectionModel.java:89-115); updateProofStatus then sets
        // proofLoaded=false, which re-enables the proof-gated menu items
        selectionModel.setSelectedProof(null);
        NotificationManagerF.getInstance().notify("Proof abandoned.", Kind.INFO);
    }

    /**
     * menu: opens the active settings of the selected proof (Swing
     * {@code ShowActiveSettingsAction.actionPerformed}, ShowActiveSettingsAction.java:32-47: the
     * "All active settings" {@code ViewSettingsDialog} over the {@code SettingsTreeModel}).
     */
    private void showActiveSettings() {
        Proof proof = selectionModel.getSelectedProof();
        if (proof == null) {
            return; // the item is disabled without a proof (Swing enableWhenProofLoaded)
        }
        ActiveSettingsDialogF.show(stage, proof);
    }

    /**
     * menu: shows the statistics of the selected proof (Swing
     * {@code ShowProofStatistics.actionPerformed}, ShowProofStatistics.java:69-78: non-modal
     * {@code Proof Statistics} window).
     */
    private void showProofStatistics() {
        Proof proof = selectionModel.getSelectedProof();
        if (proof == null) {
            return; // the item is disabled without a proof (Swing enableWhenProofLoaded)
        }
        ProofStatisticsDialogF.show(stage, proof);
    }

    /**
     * menu: shows the type hierarchy known to the selected proof (Swing
     * {@code ShowKnownTypesAction.showTypeHierarchy}, ShowKnownTypesAction.java:47-83: the modal
     * "Known types for this proof" dialog with the {@code ClassTree} of the proof's services).
     */
    private void showKnownTypes() {
        Proof proof = selectionModel.getSelectedProof();
        if (proof == null) {
            return; // the item is disabled without a proof (Swing enableWhenProofLoaded)
        }
        KnownTypesDialogF.show(stage, proof);
    }

    // menu: MP1/MP2 — expected entries of the Proof menu (system property
    // {@code key.fx.verify.menuparity}; MainWindow.createProofMenu :1082-1142, and the
    // Automation submenu entries of MainWindow.createAutomationActions :814-827 since MP2).
    // Table rows are leaf items, plain separators (the {@code "---"} row) or submenu names whose
    // own children are checked recursively; MP4/MP5 can extend the tables for the other menus.
    private static final String[][] PROOF_MENU_EXPECTED = {
        { "Automation", "Start Automatic Proof", "Stop Automatic Proof", "Full Automation",
            "Structured Automation", "Structured Automation (Prep. Only)",
            "Script-aware Auto" },
        { "Goal Back" },
        { "Prune Proof" },
        { "Abandon Proof" },
        { "---" },
        { "Search in Proof Tree" },
        { "Search in Sequent" },
        { "Search Next" },
        { "Search Previous" },
        { "Search Mode", "Highlight", "Hide", "Regroup" },
        { "---" },
        { "Show Used Contracts" },
        { "Show All Active Settings" },
        { "Show Proof Statistics" },
        { "Show Known Types" },
    };

    // menu: MP3c — expected View menu entries in the Swing order of MainWindow.createViewMenu
    // (:985-1064; Select Goal children from createSelectionMenu :1069-1074). The FX-only extras
    // between the parity entries (OriginLabelsF cluster, Theme, Font Size, Layout, Log View,
    // Soundiness, plain separators) are not listed: the walker skips unlisted built entries and
    // only asserts that the listed ones occur in this relative order.
    private static final String[][] VIEW_MENU_EXPECTED = {
        { "Pretty Print" },
        { "Unicode Symbols" },
        { "Syntax Highlighting" },
        { "Show Tooltips in Sequent View" },
        { "Show Tooltips in Source View" },
        { "Show Tooltips in Proof Tree" },
        { "ToolTip Options…" },
        { "Select Goal", "Select Goal Above", "Select Goal Below" },
        { "Back" },
        { "Forward" },
    };

    // menu: MP4 — expected Options menu entries in the Swing order of MainWindow.createOptionsMenu
    // (:1144-1161: Settings, SMT Solvers…, ─sep─, Confirm Exit, Auto Save Proofs, Minimize
    // Interaction, Right Click for Proof Macros, Ensure Source Consistency). The FX-only extras
    // between the parity entries ("Reset Dock Layout" and the two plain separators) are not
    // listed: the walker skips unlisted built entries and only asserts that the listed ones
    // occur in this relative order.
    private static final String[][] OPTIONS_MENU_EXPECTED = {
        { "Settings" },
        { "SMT Solvers…" },
        { "Confirm Exit" },
        { "Auto Save Proofs" },
        { "Minimize Interaction" },
        { "Right Click for Proof Macros" },
        { "Ensure Source Consistency" },
    };

    // menu: MP5 — expected File menu entries in the FX order after the MP5 inserts (the Swing
    // {@code MainWindow.createFileMenu} :991-1031 order with the port's existing grouping:
    // example/open/reload/edit-last-opened | proof mgmt/load-taclets/Prove | save/quick |
    // recent | exit). The three Prove submenu entries are the always-present ones; "Run All
    // Proofs" sits behind the BULK_UI_TEST feature flag (off by default) and is therefore not
    // part of the table.
    private static final String[][] FILE_MENU_EXPECTED = {
        { "Open Example…" },
        { "Open File…" },
        { "Reload" },
        { "Edit Last Opened File" },
        { "Proof Management…" },
        { "Load User Defined Taclets…" },
        { "Prove", "Load User Defined Taclets for Proving", "Load KeY Taclets",
            "Lemma Generation (Batch Mode)" },
        { "Save File…" },
        { "Save Bundle…" },
        { "Quick Save" },
        { "Quick Load" },
        { "Recent Files" },
        { "Exit" },
    };

    // menu: MP5 — expected About menu entries in the Swing order of MainWindow.createHelpMenu
    // (:1163-1174).
    private static final String[][] ABOUT_MENU_EXPECTED = {
        { "About KeY…" },
        { "KeY Homepage" },
        { "Send Feedback…" },
        { "Create Github Issue" },
        { "License…" },
    };

    /**
     * menu: MP1/MP3/MP4/MP5 — menu parity self test (system property
     * {@code key.fx.verify.menuparity},
     * run after a proof load like the other verify hooks): builds the menu bar and emits one
     * marker line per asserted menu, each ending in PASS or FAIL.
     */
    private void verifyMenuParity() {
        logMenuParity("Proof", verifyMenuParityReport("Proof", PROOF_MENU_EXPECTED));
        logMenuParity("View", verifyMenuParityReport("View", VIEW_MENU_EXPECTED));
        logMenuParity("Options", verifyMenuParityReport("Options", OPTIONS_MENU_EXPECTED));
        logMenuParity("File", verifyMenuParityReport("File", FILE_MENU_EXPECTED));
        logMenuParity("About", verifyMenuParityReport("About", ABOUT_MENU_EXPECTED));
    }

    private void logMenuParity(String menuName, String report) {
        LOGGER.info("Menu parity verification ({}): {}", menuName, report);
        NotificationManagerF.getInstance()
                .notify("Menu parity verification (" + menuName + "): " + report,
                    report.endsWith("PASS") ? Kind.INFO : Kind.ERROR);
    }

    /**
     * menu: builds the {@link #buildMenuBar() menu bar} and checks the Proof menu entries
     * (compatibility entry point: same table and report as the Proof part of
     * {@link #verifyMenuParity()}).
     *
     * @return {@code "PASS - <n> items, found: <comma list>"} or
     *         {@code "FAIL - missing: <list>"}
     */
    String verifyMenuParityReport() {
        return verifyMenuParityReport("Proof", PROOF_MENU_EXPECTED);
    }

    /**
     * menu: builds the {@link #buildMenuBar() menu bar} and checks one menu against an expected
     * table. A row may be a leaf item, a plain separator (the {@code "---"} row) or a submenu
     * name ({@code "Search Mode"}) whose own children are checked recursively, in their order.
     * Built entries that are not listed in the table are skipped.
     *
     * @return {@code "PASS - <n> items, found: <comma list>"} or
     *         {@code "FAIL - missing: <list>"}
     */
    String verifyMenuParityReport(String menuName, String[][] expected) {
        MenuBar menuBar = buildMenuBar();
        Menu menu = menuBar.getMenus().stream().filter(m -> menuName.equals(m.getText()))
                .findFirst().orElse(null);
        if (menu == null) {
            return "FAIL - missing: <" + menuName + " menu>";
        }
        List<String> present = new ArrayList<>();
        List<String> missing = new ArrayList<>();
        List<MenuItem> remaining = new ArrayList<>(menu.getItems());
        for (String[] row : expected) {
            String label = row[0];
            if ("---".equals(label)) {
                // a separator has no text; match the control type directly
                int sepIndex = -1;
                for (int i = 0; i < remaining.size(); i++) {
                    if (remaining.get(i) instanceof SeparatorMenuItem) {
                        sepIndex = i;
                        break;
                    }
                }
                if (sepIndex < 0) {
                    missing.add("separator");
                } else {
                    present.add("separator");
                    remaining = new ArrayList<>(
                        remaining.subList(sepIndex + 1, remaining.size()));
                }
                continue;
            }
            int index = indexOfItem(remaining, label);
            if (index < 0) {
                missing.add(label);
                continue;
            }
            present.add(label);
            MenuItem node = remaining.get(index);
            if (node instanceof Menu submenu && row.length > 1) {
                // check the submenu's entries in their order (e.g. Automation, Search Mode,
                // Select Goal)
                List<MenuItem> children = new ArrayList<>(submenu.getItems());
                for (int i = 1; i < row.length; i++) {
                    int childIndex = indexOfItem(children, row[i]);
                    if (childIndex < 0) {
                        missing.add(label + " > " + row[i]);
                    } else {
                        present.add(label + " > " + row[i]);
                        children = new ArrayList<>(
                            children.subList(childIndex + 1, children.size()));
                    }
                }
            }
            remaining = new ArrayList<>(remaining.subList(index + 1, remaining.size()));
        }
        String found = String.join(", ", present);
        if (missing.isEmpty()) {
            return "PASS - " + present.size() + " items, found: " + found;
        }
        return "FAIL - missing: " + String.join(", ", missing) + " (found " + found + ")";
    }

    /** menu: index of the first remaining menu item with the given text, or -1. */
    private static int indexOfItem(List<MenuItem> items, String text) {
        for (int i = 0; i < items.size(); i++) {
            MenuItem item = items.get(i);
            if (text.equals(item.getText())) {
                return i;
            }
        }
        return -1;
    }

    private Menu buildOptionsMenu() {
        Menu options = new Menu("Options");
        // menu: MP4 — Swing MainWindow.createOptionsMenu :1144-1161: Settings, SMT Solvers…
        // (SMTOptionsAction → settings dialog on the SMT panel), separator, then the five check
        // items; the FX-only "Reset Dock Layout" extra is kept between two separators (Settings,
        // SMT Solvers…, ─sep─, Reset Dock Layout, ─sep─, Confirm Exit, Auto Save Proofs,
        // Minimize Interaction, Right Click for Proof Macros, Ensure Source Consistency).
        options.getItems().addAll(
            menuItem("Settings",
                "de.uka.ilkd.key.gui.settings.SettingsManager$ShowSettingsAction",
                IconFactoryF.Key.CONFIGURE, this::openSettings),
            menuItem("SMT Solvers…", "de.uka.ilkd.key.gui.actions.SMTOptionsAction",
                IconFactoryF.Key.TOOLBOX, this::showSMTOptions),
            new SeparatorMenuItem(),
            menuItem("Reset Dock Layout", this::resetLayout),
            new SeparatorMenuItem(),
            confirmExitToggle(),
            autoSaveProofsToggle(),
            minimizeInteractionToggle(),
            rightClickMacroToggle(),
            ensureSourceConsistencyToggle());
        return options;
    }

    /**
     * menu: MP4 — SMT Solvers… opens the settings dialog on the SMT panel (Swing
     * SMTOptionsAction, SMTOptionsAction.java:27-28: {@code
     * SettingsManager.getInstance().showSettingsDialog(mainWindow, SettingsManager.SMT_SETTINGS)};
     * here the provider registered as {@link SettingsManagerF#SMT_SETTINGS} is selected in the
     * settings tree, SettingsManagerF.java:169-177).
     */
    private void showSMTOptions() {
        SettingsManagerF.getInstance().showSettingsDialog(this, SettingsManagerF.SMT_SETTINGS);
    }

    /**
     * menu: MP4 — Confirm Exit check item (Swing ToggleConfirmExitAction,
     * ToggleConfirmExitAction.java:20-31): the selected state mirrors
     * {@code ViewSettings.confirmExit()} and the action writes it back.
     */
    private CheckMenuItem confirmExitToggle() {
        ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        CheckMenuItem item = new CheckMenuItem("Confirm Exit");
        item.setSelected(vs.confirmExit());
        item.setOnAction(e -> vs.setConfirmExit(item.isSelected()));
        return item;
    }

    /**
     * loadingexit (P1) — Exit (Swing {@code ExitMainAction.exitMain}, ExitMainAction.java:55-66,
     * reached from the File menu <em>and</em> the window close button, MainWindow.java:366): when
     * the Confirm Exit view setting is on (the Options menu toggle above), asks
     * {@code Really Quit?} first.
     */
    private void exitApplication() {
        ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        if (vs.confirmExit()) {
            Alert alert = new Alert(AlertType.CONFIRMATION, "Really Quit?\n", ButtonType.YES,
                ButtonType.NO);
            alert.setTitle("Exit");
            alert.setHeaderText(null);
            alert.initOwner(stage);
            Optional<ButtonType> answer = alert.showAndWait();
            if (answer.isEmpty() || answer.get() != ButtonType.YES) {
                return;
            }
        }
        exitApplicationWithoutInteraction();
    }

    /**
     * loadingexit (P1) — Swing {@code ExitMainAction.exitMainWithoutInteraction},
     * ExitMainAction.java:87-101: recent-files store save, mediator shutdown event, preferences
     * sync and {@code System.exit(0)} (the {@code exitSystem} flag of the standalone
     * application). The FX port: the recent-files store is saved here (the
     * colors/keystrokes/docking stores persist via their own shutdown hooks, which
     * {@code System.exit(0)} still runs); and {@code System.exit(0)} is required because
     * background threads of a running solver or verification would otherwise keep the process
     * alive after {@link Platform#exit()}.
     * <p>
     * KNOWN-SIMPLIFIED: the Swing mediator shutdown event ({@code fireShutDown} notifying the
     * {@code GUIListener}s) has no FX seam — {@link KeYMediatorF} has no GUI listener registry,
     * so the FX port omits the event.
     */
    private void exitApplicationWithoutInteraction() {
        recentFiles.save();
        LOGGER.info("Have a nice day.");
        Platform.exit();
        System.exit(0);
    }

    /**
     * menu: MP4 — Auto Save Proofs check item (Swing {@code AutoSave},
     * AutoSave.java:14-33): the initial state is {@code autoSavePeriod() > 0} (AutoSave.java:22-24)
     * and the action writes {@code setAutoSave(2000)} / {@code setAutoSave(0)}
     * (AutoSave.java:29-31;
     * Swing {@code AutoSave.DEFAULT_PERIOD = 2000}, AutoSave.java:16 — key.ui, not importable into
     * this module, hence the inlined constant).
     * // menu: MP7 — the timer wiring is no longer deferred: the action arms/disarms the
     * // {@link AutoSaver} through {@link #applyAutoSave(int)} (Swing AutoSave.java:31 calls
     * // getMediator().setAutoSave(p), KeYMediator.java:148-150); arming is also applied at
     * // startup from the persisted period (see {@link #initialize()}).
     */
    private CheckMenuItem autoSaveProofsToggle() {
        GeneralSettings gs = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
        CheckMenuItem item = new CheckMenuItem("Auto Save Proofs");
        item.setSelected(gs.autoSavePeriod() > 0);
        item.setOnAction(
            e -> {
                int period = item.isSelected() ? DEFAULT_AUTO_SAVE_PERIOD : 0;
                gs.setAutoSave(period);
                applyAutoSave(period);
            });
        return item;
    }

    /**
     * menu: MP7 — arms or disarms the {@link AutoSaver} (Swing {@code KeYMediator.setAutoSave},
     * KeYMediator.java:148-150, called by {@code AutoSave} with the new period, AutoSave.java
     * :29-31): the saver is created with the given interval and registered on the window's UI
     * control as a {@code ProverTaskListener} so the core's proof runs deliver it the task
     * events — the FX equivalent of the Swing {@code MediatorProofControl.AutoModeWorker}
     * registration (MediatorProofControl.java:209-211). The saver field itself lives on the
     * mediator ({@code KeYMediatorF#getAutoSaver}), which hands it every newly selected proof
     * from {@code setProof}.
     *
     * @param period the save interval in proof steps, 0 disables auto save
     */
    private void applyAutoSave(int period) {
        AutoSaver oldSaver = mediator.getAutoSaver();
        if (oldSaver != null) {
            getUserInterfaceControl().removeProverTaskListener(oldSaver);
        }
        mediator.setAutoSave(period);
        AutoSaver newSaver = mediator.getAutoSaver();
        if (newSaver != null) {
            getUserInterfaceControl().addProverTaskListener(newSaver);
        }
    }

    /**
     * menu: MP7 — auto-save self-test helper: {@code AutoSaver} (key.core) stores the proof from
     * {@code setProof} in a private field without a getter (AutoSaver.java:40, :102-104); the
     * proof identity is read reflectively for the {@code key.fx.verify.autosave} assertion.
     *
     * @param saver the armed auto saver
     * @return the proof the saver received, or {@code null} on failure/reflection error
     */
    private static Object readAutoSaveProof(AutoSaver saver) {
        try {
            Field proofField = AutoSaver.class.getDeclaredField("proof");
            proofField.setAccessible(true);
            return proofField.get(saver);
        } catch (ReflectiveOperationException e) {
            LOGGER.error("Auto save verification: cannot read AutoSaver.proof", e);
            return null;
        }
    }

    /** menu: MP4 — Swing {@code AutoSave.DEFAULT_PERIOD} (key.ui), see autoSaveProofsToggle(). */
    private static final int DEFAULT_AUTO_SAVE_PERIOD = 2000;

    /**
     * menu: MP4 — Minimize Interaction check item (Swing {@code MinimizeInteraction},
     * MinimizeInteraction.java:17-73, display name "Minimize Interaction"): the selected state
     * mirrors and writes the {@code GeneralSettings} taclet filter and applies it to the proof
     * control of the currently loaded environment.
     * // menu: MP7 — the proof-control wiring is no longer deferred: the toggle applies the flag
     * // through {@link #applyMinimizeInteraction(ProofControl)} (Swing
     * // MinimizeInteraction.handleClickEvent, MinimizeInteraction.java:57-66:
     * // mainWindow.getUserInterface().getProofControl().setMinimizeInteraction(b)).
     */
    private CheckMenuItem minimizeInteractionToggle() {
        GeneralSettings gs = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
        CheckMenuItem item = new CheckMenuItem("Minimize Interaction");
        item.setSelected(gs.getTacletFilter());
        item.setOnAction(e -> {
            // menu: MP7 — the flag is written first, then applied to the proof control of the
            // loaded environment (Swing MinimizeInteraction.handleClickEvent writes the settings
            // after updateMainWindow; here the settings change must happen first so the helper
            // reads the new value)
            gs.setTacletFilter(item.isSelected());
            applyMinimizeInteraction(
                lastEnvironment == null ? null : lastEnvironment.getProofControl());
        });
        return item;
    }

    /**
     * menu: MP7 — applies the persisted Minimize Interaction flag to the given proof control
     * (Swing {@code MinimizeInteraction.updateMainWindow}, MinimizeInteraction.java:64-66: {@code
     * mainWindow.getUserInterface().getProofControl().setMinimizeInteraction(b)}); the core honors
     * the flag in {@code AbstractProofControl} (only complete rule applications are offered to the
     * user). No-op for a {@code null} control (no proof loaded — the flag is applied to the next
     * attached proof control by the load-success path).
     *
     * @param pc the proof control to update, may be {@code null}
     */
    private void applyMinimizeInteraction(@Nullable ProofControl pc) {
        if (pc == null) {
            return;
        }
        boolean flag = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
                .getTacletFilter();
        pc.setMinimizeInteraction(flag);
    }

    /**
     * menu: MP4 — Right Click for Proof Macros check item (Swing RightMouseClickToggleAction,
     * RightMouseClickToggleAction.java:22-33): the selected state mirrors
     * {@code GeneralSettings.isRightClickMacro()} and the action writes
     * {@code setRightClickMacros} back.
     * // menu: MP7 — the right-click behavior is no longer deferred: while the flag is set the
     * // sequent view shows the proof-macro popup instead of the term context menu
     * // (SequentViewF.buildRightClickMenu, Swing CurrentGoalViewListener.java:54-67 /
     * ProofMacroMenu).
     */
    private CheckMenuItem rightClickMacroToggle() {
        GeneralSettings gs = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
        CheckMenuItem item = new CheckMenuItem("Right Click for Proof Macros");
        item.setSelected(gs.isRightClickMacro());
        item.setOnAction(e -> gs.setRightClickMacros(item.isSelected()));
        return item;
    }

    /**
     * menu: MP4 — Ensure Source Consistency check item (Swing
     * EnsureSourceConsistencyToggleAction, EnsureSourceConsistencyToggleAction.java:37-48): the
     * selected state mirrors {@code GeneralSettings.isEnsureSourceConsistency()} and the action
     * writes {@code setEnsureSourceConsistency} back.
     * // menu: MP7 — the flag is honored at runtime by the core and the FX soundiness report:
     * // AbstractProblemLoader.createFileRepo (AbstractProblemLoader.java:400-409) picks the
     * // DiskFileRepo (source-cache backend) over the SimpleFileRepo when it is set, and the FX
     * // SoundinessAnalyzer warns when it is off (SoundinessAnalyzer.java:377-383). The Swing
     * // info dialog of the toggle action (EnsureSourceConsistencyToggleAction.java:42-47) is
     * // ported below (dialogs marker, audit item A9).
     */
    private CheckMenuItem ensureSourceConsistencyToggle() {
        GeneralSettings gs = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
        CheckMenuItem item = new CheckMenuItem("Ensure Source Consistency");
        item.setSelected(gs.isEnsureSourceConsistency());
        item.setOnAction(e -> {
            // dialogs (P2b, A9): the Swing toggle shows an info dialog when a proof is loaded —
            // the change becomes effective with the NEXT load (Swing
            // EnsureSourceConsistencyToggleAction.actionPerformed:42-47)
            if (mediator.ensureProofLoaded()) {
                Alert info = new Alert(Alert.AlertType.INFORMATION,
                    "Your changes will become effective when the next problem is loaded.\n");
                info.setTitle("Allow Proof Bundle Saving");
                info.setHeaderText("Allow Proof Bundle Saving");
                info.initOwner(getStage());
                info.show();
            }
            gs.setEnsureSourceConsistency(item.isSelected());
        });
        return item;
    }

    /**
     * menu: MP5 — the About menu in the Swing order of {@code MainWindow.createHelpMenu}
     * (:1163-1174): About KeY, KeY Homepage, Send Feedback, Create Github Issue, License. The
     * browser actions go through the {@link HelpFacadeF} browser seam (host services); the
     * feedback dialog is the minimal {@link FeedbackDialogF} port of the Swing
     * {@code SendFeedbackAction}.
     */
    private Menu buildAboutMenu() {
        Menu about = new Menu("About");
        about.getItems().addAll(
            menuItem("About KeY…", "de.uka.ilkd.key.gui.actions.AboutAction", this::showAbout),
            menuItem("KeY Homepage",
                "de.uka.ilkd.key.gui.actions.KeYProjectHomepageAction",
                () -> HelpFacadeF.openExternal(KEY_PROJECT_URL)),
            menuItem("Send Feedback…", "de.uka.ilkd.key.gui.actions.MenuSendFeedackAction",
                () -> FeedbackDialogF.show(stage)),
            menuItem("Create Github Issue",
                "de.uka.ilkd.key.gui.actions.CreateGithubIssueAction",
                () -> HelpFacadeF.openExternal(GITHUB_ISSUE_URL)),
            menuItem("License…", "de.uka.ilkd.key.gui.actions.LicenseAction",
                IconFactoryF.Key.INFO_VIEW, this::showLicense));
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
        // extension: MP9.0 — the status-line controls contributed by the FX extensions are
        // appended at the right end of the status bar, after the theme/font-size label (Swing
        // MainWindow.createStatusBar / KeYGuiExtensionFacade.getStatusLineComponents,
        // KeYGuiExtensionFacade.java:325-333); shown only when an extension contributes
        // controls.
        List<Control> extensionStatusControls = KeYGuiExtensionFacadeF.getStatusLineControls();
        if (!extensionStatusControls.isEmpty()) {
            bar.getChildren().addAll(extensionStatusControls);
        }
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

    /**
     * smalldialogs: opens the soundiness report for the selected proof (Swing
     * {@code ShowSoundinessAction.actionPerformed}: modal {@code SoundinessDialog} for
     * {@code mediator.getSelectedProof()}, no-op without a proof).
     */
    private void showSoundinessReport() {
        Proof proof = selectionModel.getSelectedProof();
        if (proof == null) {
            return; // the item is disabled without a proof (Swing enableWhenProofLoaded)
        }
        new SoundinessDialogF(stage, proof).showCenteredOnOwner();
    }

    /**
     * smalldialogs: self test of the soundiness report (system property
     * {@code key.fx.verify.soundiness}, run after a proof load like the other proof-dependent
     * verify hooks): the report of the loaded proof must contain the four report sections, then
     * the dialog itself is opened for visual inspection (close it to continue).
     */
    private void runSoundinessVerification() {
        Proof proof = selectionModel.getSelectedProof();
        if (proof == null) {
            LOGGER.info("Soundiness verification: skipped, no proof loaded FAIL");
            NotificationManagerF.getInstance()
                    .notify("Soundiness verification: skipped, no proof loaded FAIL", Kind.ERROR);
            return;
        }
        String html = SoundinessAnalyzer.generateHTMLReport(proof);
        boolean sectionsOk = html.contains("KeY Soundiness Report")
                && html.contains("1. General KeY Soundiness")
                && html.contains("2. Taclet Option Soundiness")
                && html.contains("3. Proof Tree Analysis");
        String report = "chars=" + html.length() + " sections=" + sectionsOk
            + (sectionsOk ? " PASS" : " FAIL");
        LOGGER.info("Soundiness verification: {}", report);
        NotificationManagerF.getInstance()
                .notify("Soundiness verification: " + report,
                    sectionsOk ? Kind.INFO : Kind.ERROR);
        if (sectionsOk) {
            new SoundinessDialogF(stage, proof).showCenteredOnOwner();
        }
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
