/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.plugins.caching.fx;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.scene.control.Alert;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.control.ButtonType;
import javafx.scene.control.CheckMenuItem;
import javafx.scene.control.Control;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.ToggleButton;
import javafx.scene.control.Tooltip;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.gui.fx.IssueDialogF;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.gui.fx.settings.SettingsManagerF;
import de.uka.ilkd.key.gui.fx.settings.SettingsProviderF;
import de.uka.ilkd.key.gui.plugins.caching.settings.ProofCachingSettings;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.TryCloseMacro;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.RuleAppListener;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.proof.reference.ReferenceSearcher;
import de.uka.ilkd.key.proof.replay.CopyingProofReplayer;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.key_project.prover.engine.ProverTaskListener;
import org.key_project.prover.engine.TaskFinishedInfo;
import org.key_project.prover.engine.TaskStartedInfo;
import org.key_project.prover.engine.impl.DefaultProver;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.javafx.FxUtil;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The proof-caching extension, FX port of {@code de.uka.ilkd.key.gui.plugins.caching.
 * CachingExtension} (Swing CachingExtension.java:63-341) registered via the service-loader file
 * {@code META-INF/services/de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF}.
 * <p>
 * The Swing original contributes the caching UI through the Swing extension capabilities
 * (main-menu action, toolbar, status line, sequent context actions, settings panel and the startup
 * hooks). This port implements the same surface with the FX SPI {@link KeYGuiExtensionF}: a
 * separate "Caching" menu with the toggle and the settings entries, the toolbar toggle, a
 * status-line button showing the number of cached (closed-by-reference) goals, the four
 * proof-caching context items on the sequent term menu, the "Proof Caching" settings panel and
 * the startup wiring (selection tracking, automatic reference search after rule applications, the
 * copy/reopen-on-dispose behaviour).
 * <p>
 * The reused *logic* classes of {@code keyext.caching} are kept untouched
 * ({@link ProofCachingSettings}, {@link ReferenceSearcher}, the {@code ClosedBy} registry);
 * only the UI surface is ported.
 *
 * @author Arne Keller (Swing original)
 * @author MP9.1 extension SPI port (FX)
 */
@KeYGuiExtensionF.Info(name = "Proof Caching", optional = true,
    description = "Functionality related to reusing previous proof results in similar proofs",
    experimental = false)
public class CachingExtensionF
        implements KeYGuiExtensionF, KeYGuiExtensionF.MainMenuF, KeYGuiExtensionF.ToolbarF,
        KeYGuiExtensionF.StatusLineF, KeYGuiExtensionF.ContextMenuF, KeYGuiExtensionF.SettingsF,
        KeYGuiExtensionF.StartupF {
    private static final Logger LOGGER = LoggerFactory.getLogger(CachingExtensionF.class);

    /**
     * The reused persisted caching settings (Swing {@code ProofCachingSettings}, singleton
     * registered into the {@link ProofIndependentSettings}). Owned by the FX module via
     * {@link CachingSettingsProviderF#getCachingSettings()} (KNOWN-SIMPLIFIED: the Swing keyext
     * {@code CachingSettingsProvider.getCachingSettings()} is not loadable on the FX module's
     * compile path; see {@link CachingSettingsProviderF}).
     */
    private final ProofCachingSettings settings = CachingSettingsProviderF.getCachingSettings();

    /**
     * @return the caching settings used by the automatic reference search and the
     *         prune/dispose handlers (package-private for the unit test asserting the
     *         module-owned singleton identity)
     */
    ProofCachingSettings settings() {
        return settings;
    }

    /**
     * The global runtime off-switch, mirroring the selected state of the Swing
     * {@code CachingToggleAction} (CachingToggleAction.java:26-38: a checked action enabled by
     * default; {@code getProofCachingEnabled()} ANDs it with the settings flag and the
     * single-core gate). The checkbox of the menu and the toolbar toggle share this property.
     */
    private final BooleanProperty toggle = new SimpleBooleanProperty(this, "cachingToggle", true);

    /**
     * Whether the multi-core prover is active (Swing {@code SingleCoreFeatureGate.isActive},
     * SingleCoreFeatureGate.java:88-97: proof caching is a single-core-only feature and is greyed
     * out while the parallel prover is enabled). Refreshed from the
     * {@code GeneralSettings.PARALLEL_PROVER_ENABLED} property change events.
     */
    private final BooleanProperty multiCoreActive = new SimpleBooleanProperty(this,
        "multiCoreProverActive", false);

    /**
     * The menu checkbox of the main-menu toggle, created lazily on first use
     * ({@link #menuToggleItem()}). KNOWN-SIMPLIFIED: instantiation is deferred because
     * constructing JavaFX controls requires the FX toolkit, but the SPI may instantiate the
     * provider before any display is up (headless unit tests, verify hooks); the host builds
     * the menus/toolbar/status line at startup, when the toolkit is already running.
     */
    private @Nullable CheckMenuItem toggleMenuItem;

    /**
     * the toolbar toggle (bound to {@link #toggle}, created lazily — see
     * {@link #toolbarToggleButton()})
     */
    private @Nullable ToggleButton toggleButton;

    /**
     * the singleton status-line button (Swing {@code ReferenceSearchButton}, created lazily —
     * see {@link #statusLineButton()})
     */
    private @Nullable CachingStatusButtonF statusButton;

    /**
     * the settings panel contributed into the settings dialog (Swing
     * {@code CachingSettingsProvider}, created lazily — see {@link #settingsPanelProvider()})
     */
    private @Nullable SettingsProviderF settingsProvider;

    /**
     * @return the "Proof Caching" menu checkbox, created and bound to {@link #toggle} on first
     *         use
     */
    private CheckMenuItem menuToggleItem() {
        CheckMenuItem item = toggleMenuItem;
        if (item == null) {
            item = new CheckMenuItem("Proof Caching");
            item.setSelected(toggle.get());
            // the checked state is synced into {@link #toggle} by the binding
            item.selectedProperty().bindBidirectional(toggle);
            item.disableProperty().bind(multiCoreActive);
            toggleMenuItem = item;
        }
        return item;
    }

    /**
     * @return the toolbar toggle button, created and bound to {@link #toggle} on first use
     */
    private ToggleButton toolbarToggleButton() {
        ToggleButton button = toggleButton;
        if (button == null) {
            button = new ToggleButton("Proof Caching");
            button.selectedProperty().bindBidirectional(toggle);
            button.disableProperty().bind(multiCoreActive);
            toggleButton = button;
        }
        return button;
    }

    /**
     * @return the singleton status-line button, created on first use; the same instance is
     *         returned on every call, so the host's status-bar membership check holds
     */
    private CachingStatusButtonF statusLineButton() {
        CachingStatusButtonF button = statusButton;
        if (button == null) {
            button = new CachingStatusButtonF();
            statusButton = button;
        }
        return button;
    }

    /**
     * @return the settings panel provider contributed into the settings dialog (Swing
     *         {@code CachingSettingsProvider}), created on first use
     */
    private SettingsProviderF settingsPanelProvider() {
        SettingsProviderF provider = settingsProvider;
        if (provider == null) {
            provider = new CachingSettingsProviderF();
            settingsProvider = provider;
        }
        return provider;
    }

    /**
     * Proofs tracked for automatic reference search (Swing {@code trackedProofs},
     * CachingExtension.java:83-85: proofs seen by the selection listener are registered with the
     * rule-app / dispose / prune listeners). Also the source for the "currently opened proofs"
     * of {@link ReferenceSearcher#findPreviousProof}.
     */
    private final Set<Proof> trackedProofs = Collections.synchronizedSet(new HashSet<>());

    /**
     * Whether to try to close the current proof (by caching) after a rule application; false
     * while certain macros (like the "close provable goals" macro) are running (Swing
     * {@code tryToClose}, CachingExtension.java:78, maintained through the
     * {@link ProverTaskListener} hooks).
     */
    private volatile boolean tryToClose = false;

    /** the handler for prunes into referenced branches (Swing {@code CachingPruneHandler}) */
    private @Nullable CachingPruneHandlerF cachingPruneHandler;

    /** the window the extension is attached to, wired in {@link #init} */
    private @Nullable MainWindowF window;

    /** the mediator the extension is attached to, wired in {@link #init} */
    private @Nullable KeYMediatorF mediator;

    /**
     * The selection listener tracking the loaded proofs and refreshing the status button (Swing
     * {@code CachingExtension.selectedProofChanged}, CachingExtension.java:130-139).
     */
    private final KeYSelectionListener selectionListener = new KeYSelectionListener() {
        @Override
        public void selectedProofChanged(KeYSelectionEvent<Proof> event) {
            trackProof(event.getSource().getSelectedProof());
        }

        @Override
        public void selectedNodeChanged(KeYSelectionEvent<Node> event) {
            updateGUIState(event.getSource().getSelectedProof());
        }
    };

    /**
     * The rule-app listener performing the automatic reference search (Swing
     * {@code CachingExtension.ruleApplied}, CachingExtension.java:142-187).
     */
    private final RuleAppListener ruleAppListener = this::ruleApplied;

    /** removes disposed proofs from the tracking set (Swing {@code proofDisposing}). */
    private final ProofDisposedListener disposeListener = new ProofDisposedListener() {
        @Override
        public void proofDisposing(ProofDisposedEvent event) {
            trackedProofs.remove(event.getSource());
        }

        @Override
        public void proofDisposed(ProofDisposedEvent event) {
        }
    };

    /**
     * The prover-task listener maintaining the {@code tryToClose} flag and re-opening goals that
     * were closed by reference after a failed macro/prover run (Swing
     * {@code CachingExtension.taskStarted/taskProgress/taskFinished},
     * CachingExtension.java:236-270).
     */
    private final ProverTaskListener proverTaskListener = new ProverTaskListener() {
        @Override
        public void taskStarted(TaskStartedInfo info) {
            if (info.kind().equals(TaskStartedInfo.TaskKind.Macro)
                    && info.message().equals(new TryCloseMacro().getName())) {
                tryToClose = false;
            }
        }

        @Override
        public void taskProgress(int position) {
            tryToClose = true;
        }

        @Override
        public void taskFinished(TaskFinishedInfo info) {
            onTaskFinished(info);
        }
    };

    @Override
    public void init(MainWindowF window, KeYMediatorF mediator) {
        // extension: MP9.1 — Swing CachingExtension.preInit (CachingExtension.java:190-194:
        // mediator/selection listener/task listener wiring) + init (:197-199: the prune
        // handler). The FX host calls init once after discovery; every hook is null-guarded
        // and the UI refreshes are marshalled onto the FX thread.
        attach(window, mediator);
        if (mediator != null) {
            mediator.getSelectionModel().addKeYSelectionListener(selectionListener);
        }
        if (window != null) {
            window.getUserInterfaceControl().addProverTaskListener(proverTaskListener);
        }
        cachingPruneHandler = new CachingPruneHandlerF(this);
        // single-core gate: grey out the single-core-only contributions while the multi-core
        // prover is enabled (Swing SingleCoreFeatureGate, SingleCoreFeatureGate.java:53-60).
        multiCoreActive.set(isMultiCoreActive());
        GeneralSettings general = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
        general.addPropertyChangeListener(GeneralSettings.PARALLEL_PROVER_ENABLED,
            evt -> {
                multiCoreActive.set(isMultiCoreActive());
                updateGUIState(mediator == null ? null : mediator.getSelectedProof());
            });
        // initial UI state (Swing updateGUIState is called from the context actions; the button
        // is primed like Swing ReferenceSearchButton.updateState on construction).
        updateGUIState(mediator == null ? null : mediator.getSelectedProof());
    }

    /**
     * Remembers the window/mediator for the capabilities that need them (the facade hands them
     * only to {@link KeYGuiExtensionF.MainMenuF}/{@link KeYGuiExtensionF.ToolbarF}/
     * {@link KeYGuiExtensionF.StartupF}).
     */
    private void attach(MainWindowF window, KeYMediatorF mediator) {
        this.window = window;
        this.mediator = mediator;
        // the button's click runs the reference search of the whole extension (the button itself
        // never resolves proofs: the extension pushes the selected proof into
        // CachingStatusButtonF.updateState)
        statusLineButton().setOnAction(e -> runReferenceSearchFromStatus());
    }

    // ------------------------------------------------------------------
    // MainMenuF
    // ------------------------------------------------------------------

    @Override
    public List<Menu> getMenus(MainWindowF window, KeYMediatorF mediator) {
        // extension: MP9.1 — Swing CachingExtension.getMainMenuActions (CachingExtension.java:
        // 116-120) contributes the single checked CachingToggleAction; the FX SPI contributes
        // whole menus, so the toggles live in ONE new "Caching" menu (the five built-in menu
        // bars and their item sets stay untouched — key.fx.verify.menuparity keeps asserting
        // 16/24/12/7/5). The menu holds the global toggle, the persisted auto-search setting
        // and the settings-dialog opener (same items as the toolbar/status surface).
        attach(window, mediator);

        Menu caching = new Menu("Caching");
        caching.getItems().add(menuToggleItem());
        caching.getItems().add(autoSearchItem());
        caching.getItems().add(settingsItem());
        return List.of(caching);
    }

    /**
     * The persisted "Automatically search for references in auto mode" toggle of the settings
     * panel (Swing {@code ProofCachingSettings.enabled} + the {@code addCheckBox} row of
     * CachingSettingsProvider.java:73-74) as a menu checkbox.
     */
    private MenuItem autoSearchItem() {
        CheckMenuItem item =
            new CheckMenuItem("Automatically search for references in auto mode");
        item.setSelected(settings.getEnabled());
        item.setOnAction(e -> settings.setEnabled(item.isSelected()));
        return item;
    }

    /** Opens the "Proof Caching" settings panel in the settings dialog (like the HeatmapF). */
    private MenuItem settingsItem() {
        MenuItem item = new MenuItem("Proof Caching Options…");
        item.setOnAction(e -> {
            MainWindowF owner = window;
            if (owner != null) {
                SettingsManagerF.getInstance().showSettingsDialog(owner, settingsPanelProvider());
            }
        });
        return item;
    }

    // ------------------------------------------------------------------
    // ToolbarF
    // ------------------------------------------------------------------

    @Override
    public List<Control> getToolbarControls(MainWindowF window, KeYMediatorF mediator) {
        // extension: MP9.1 — Swing CachingExtension.getToolbar (CachingExtension.java:107-114):
        // the JToolBar holds the toggle button bound to the CachingToggleAction; the FX port
        // contributes the shared toggle button (with the description tooltip of the Swing
        // action, CachingToggleAction.java:23, 36-37).
        attach(window, mediator);
        ToggleButton button = toolbarToggleButton();
        button.setTooltip(
            new Tooltip("Enable or disable proof caching for currently open proofs."));
        return List.of(button);
    }

    // ------------------------------------------------------------------
    // StatusLineF
    // ------------------------------------------------------------------

    @Override
    public List<Control> getStatusLineControls() {
        // extension: MP9.1 — Swing CachingExtension.getStatusLineComponents
        // (CachingExtension.java:230-233): the ReferenceSearchButton; a singleton in the FX
        // port (same instance on every call, so the host's status bar membership check holds).
        return List.of(statusLineButton());
    }

    // ------------------------------------------------------------------
    // ContextMenuF (sequent context items)
    // ------------------------------------------------------------------

    @Override
    public List<MenuItem> getSequentContextItems(KeYMediatorF mediator, Goal goal,
            PosInSequent pos) {
        // extension: MP9.1 — Swing CachingExtension.getContextActions for
        // ContextMenuKind.SEQUENT_VIEW (CachingExtension.java:212-227): the four node actions.
        // The FX SPI hands the clicked Goal, so the actions operate on its node. Null-safe:
        // without a goal (or a goal without a node) no items are contributed.
        if (mediator == null || goal == null || goal.node() == null) {
            return List.of();
        }
        Node node = goal.node();
        List<MenuItem> items = new ArrayList<>();
        items.add(closeByReferenceItem(mediator, node));
        items.add(copyReferencedProofItem(mediator, node));
        items.add(gotoReferenceItem(mediator, node));
        items.add(removeCachingInformationItem(mediator, node));
        return items;
    }

    /**
     * "Close by reference to other proof" (Swing {@code CloseByReference}): searches the other
     * proofs for an equivalent closed branch and closes the goal(s) by registering the found
     * reference. The result message dialog is ported as a JavaFX {@link Alert}.
     */
    private MenuItem closeByReferenceItem(KeYMediatorF mediator, Node node) {
        MenuItem item = new MenuItem("Close by reference to other proof");
        item.setDisable(node.isClosed() || node.lookup(ClosedBy.class) != null);
        item.setOnAction(e -> closeByReference(mediator, node));
        return item;
    }

    private void closeByReference(KeYMediatorF mediator, Node node) {
        // nodes will be the open goals for which to perform proof caching
        List<Node> nodes = new ArrayList<>();
        if (node.leaf()) {
            nodes.add(node);
        } else {
            var iterator = node.subtreeIterator();
            while (iterator.hasNext()) {
                Node n = iterator.next();
                if (n.leaf() && !n.isClosed()) {
                    nodes.add(n);
                }
            }
        }
        List<Integer> mismatches = new ArrayList<>();
        List<Integer> matches = new ArrayList<>();
        for (Node n : nodes) {
            ClosedBy c = null;
            try {
                c = ReferenceSearcher.findPreviousProof(openProofs(), n);
            } catch (Exception exception) {
                LOGGER.warn("error during reference search", exception);
            }
            if (c != null) {
                matches.add(n.serialNr());
                Goal goal = n.proof().getOpenGoal(n);
                if (goal != null) {
                    n.proof().closeGoal(goal);
                    n.register(c, ClosedBy.class);
                }
            } else {
                mismatches.add(n.serialNr());
            }
        }
        if (!nodes.isEmpty()) {
            updateGUIState(nodes.get(0).proof());
        }
        if (!mismatches.isEmpty() || !matches.isEmpty()) {
            StringBuilder sb = new StringBuilder();
            if (!matches.isEmpty()) {
                sb.append("Cache hit found for node(s) ").append(matches);
            }
            if (!mismatches.isEmpty()) {
                if (!sb.isEmpty()) {
                    sb.append('\n');
                }
                sb.append("No matching branch found for node(s) ").append(mismatches);
            }
            showInfoAlert(sb.toString());
        }
    }

    /**
     * "Copy referenced proof steps here" (Swing {@code CopyReferencedProof}): copies the steps
     * of every leaf closed by reference into the current proof. Errors surface in the FX issue
     * dialog instead of the Swing {@code IssueDialog}.
     */
    private MenuItem copyReferencedProofItem(KeYMediatorF mediator, Node node) {
        List<Node> nodes = new ArrayList<>();
        var iterator = node.leavesIterator();
        while (iterator.hasNext()) {
            Node leaf = iterator.next();
            if (leaf.isClosed() && leaf.lookup(ClosedBy.class) != null) {
                nodes.add(leaf);
            }
        }
        MenuItem item = new MenuItem("Copy referenced proof steps here");
        item.setDisable(nodes.isEmpty());
        item.setOnAction(e -> copyReferencedProof(mediator, nodes));
        return item;
    }

    private void copyReferencedProof(KeYMediatorF mediator, List<Node> nodes) {
        for (Node node : nodes) {
            ClosedBy c = node.lookup(ClosedBy.class);
            Goal current = node.proof().getClosedGoal(node);
            if (c == null || current == null) {
                continue;
            }
            try {
                new CopyingProofReplayer(c.proof(), node.proof()).copy(c.node(), current,
                    c.nodesToSkip());
            } catch (Exception ex) {
                LOGGER.error("failed to copy proof steps", ex);
                MainWindowF owner = window;
                if (owner != null) {
                    FxUtil.runLater(
                        () -> IssueDialogF.showExceptionDialog(owner.getStage(), ex));
                }
            }
        }
        updateGUIState(mediator.getSelectedProof());
    }

    /**
     * "Go to referenced proof" (Swing {@code GotoReferenceAction}): selects the equivalent node
     * in the referenced proof.
     */
    private MenuItem gotoReferenceItem(KeYMediatorF mediator, Node node) {
        MenuItem item = new MenuItem("Go to referenced proof");
        item.setDisable(node.lookup(ClosedBy.class) == null);
        item.setOnAction(e -> {
            ClosedBy c = node.lookup(ClosedBy.class);
            if (c != null) {
                mediator.getSelectionModel().setSelectedNode(c.node());
            }
        });
        return item;
    }

    /**
     * "Re-open cached goal" (Swing {@code RemoveCachingInformationAction}): removes the caching
     * information and re-opens the goal.
     */
    private MenuItem removeCachingInformationItem(KeYMediatorF mediator, Node node) {
        MenuItem item = new MenuItem("Re-open cached goal");
        item.setDisable(node.lookup(ClosedBy.class) == null);
        item.setOnAction(e -> {
            ClosedBy c = node.lookup(ClosedBy.class);
            if (c == null) {
                return;
            }
            node.deregister(c, ClosedBy.class);
            Goal goal = node.proof().getClosedGoal(node);
            if (goal != null) {
                node.proof().reOpenGoal(goal);
            }
            // refresh selection to ensure UI is updated
            mediator.getSelectionModel().setSelectedNode(node);
        });
        return item;
    }

    // ------------------------------------------------------------------
    // SettingsF
    // ------------------------------------------------------------------

    @Override
    public SettingsProviderF getSettings() {
        // extension: MP9.1 — Swing CachingExtension.getSettings (CachingExtension.java:338-340)
        // returns the CachingSettingsProvider; the host registers it into the SettingsManagerF
        // registry (Swing SettingsManager.registerProvider).
        return settingsPanelProvider();
    }

    // ------------------------------------------------------------------
    // startup logic: automatic reference search
    // ------------------------------------------------------------------

    /**
     * Tracks a proof for automatic reference search: registers the rule-app / dispose / prune
     * listeners once per proof (Swing {@code CachingExtension.selectedProofChanged},
     * CachingExtension.java:130-139). Null-safe and idempotent.
     *
     * @param proof the currently open proof
     */
    private void trackProof(@Nullable Proof proof) {
        if (proof == null || trackedProofs.contains(proof)) {
            return;
        }
        trackedProofs.add(proof);
        proof.addRuleAppListener(ruleAppListener);
        proof.addProofDisposedListener(disposeListener);
        CachingPruneHandlerF handler = cachingPruneHandler;
        if (handler != null) {
            proof.addProofTreeListener(handler);
        }
    }

    /**
     * @return whether the single-core-only caching features are currently unavailable (Swing
     *         {@code SingleCoreFeatureGate.isActive}, SingleCoreFeatureGate.java:97-103: the
     *         multi-core prover is enabled).
     */
    private boolean isMultiCoreActive() {
        return ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
                .isParallelProverEnabled();
    }

    /**
     * @return whether proof caching is enabled for automatic runs: the runtime off-switch AND
     *         the single-core gate (Swing {@code CachingExtension.getProofCachingEnabled},
     *         CachingExtension.java:122-127).
     */
    public boolean getProofCachingEnabled() {
        return toggle.get() && !isMultiCoreActive();
    }

    /**
     * The mains entry point of the proof-caching logic, called after every rule application of
     * a tracked proof (Swing {@code CachingExtension.ruleApplied},
     * CachingExtension.java:142-187): when the runtime switches and the settings permit it, the
     * new goals of an automatic step are matched against the closed branches of the other
     * proofs and closed by reference.
     *
     * @param event the rule application event
     */
    private void ruleApplied(ProofEvent event) {
        if (!tryToClose) {
            return;
        }
        if (event.getSource().lookup(CopyingProofReplayer.class) != null) {
            // either: copy in progress, or a macro that expects the proof to really close
            return;
        }
        if (!settings.getEnabled()) {
            return;
        }
        if (!getProofCachingEnabled()) {
            return;
        }
        Proof p = event.getSource();
        if (event.getRuleAppInfo().getOriginalNode().getNodeInfo()
                .getInteractiveRuleApplication()) {
            return; // only applies to automatic proof search
        }
        ImmutableList<Goal> newGoals = event.getNewGoals();
        if (newGoals.size() <= 1) {
            return;
        }
        for (Goal goal : newGoals) {
            ClosedBy c = null;
            try {
                c = ReferenceSearcher.findPreviousProof(openProofs(), goal.node());
            } catch (Exception exception) {
                LOGGER.warn("error during reference search", exception);
            }
            if (c != null) {
                // stop automode from working on this goal
                goal.setEnabled(false);
                goal.node().register(c, ClosedBy.class);
                c.proof().addProofDisposedListenerFirst(new CopyBeforeDisposeF(c.proof(), p));
            }
        }
    }

    /**
     * The prover-task finished hook (Swing {@code CachingExtension.taskFinished},
     * CachingExtension.java:248-270): after a failed prover/macro run, re-opens goals that were
     * closed by reference, so the user can continue from an open state.
     *
     * @param info the finished task
     */
    private void onTaskFinished(TaskFinishedInfo info) {
        tryToClose = info.getSource() instanceof TryCloseMacro;
        if (tryToClose) {
            return; // try close macro was running, nothing to do here
        }
        if (!(info.getProof() instanceof Proof p) || p.isDisposed() || p.closed()
                || !(info.getSource() instanceof DefaultProver
                        || info.getSource() instanceof ProofMacro)) {
            return;
        }
        // unmark interactive goals
        if (p.countNodes() > 1 && p.openGoals().stream()
                .anyMatch(goal -> goal.node().lookup(ClosedBy.class) != null)) {
            p.openGoals().stream().filter(goal -> goal.node().lookup(ClosedBy.class) != null)
                    .forEach(g -> {
                        g.setEnabled(true);
                        g.proof().closeGoal(g);
                    });
            // statistics dialog is automatically shown (Swing); not ported
        }
    }

    // ------------------------------------------------------------------
    // status-line button behaviour
    // ------------------------------------------------------------------

    /** Updates the GUI state of the status line button (Swing {@code updateGUIState}). */
    public void updateGUIState(@Nullable Proof proof) {
        statusLineButton().updateState(proof);
    }

    /**
     * The click handler of the status-line button (Swing
     * {@code ReferenceSearchButton.actionPerformed}, ReferenceSearchButton.java:63-80):
     * searches every open goal of the selected proof for references and closes the matches by
     * registering the {@code ClosedBy} reference (with the copy-on-dispose listener).
     * <p>
     * <b>KNOWN-SIMPLIFIED:</b> the Swing original then opens the interactive
     * {@code ReferenceSearchDialog} (a table of the per-goal results with an "Apply" button that
     * copies the steps, ReferenceSearchDialog.java:25-171). The FX port shows a read-only
     * summary {@link Alert} instead; the copy of the referenced steps stays available through
     * the "Copy referenced proof steps here" context item.
     */
    private void runReferenceSearchFromStatus() {
        KeYMediatorF m = mediator;
        if (m == null) {
            return;
        }
        Proof p = m.getSelectedProof();
        if (p == null) {
            return;
        }
        int closed = 0;
        for (Goal goal : p.openEnabledGoals()) {
            ClosedBy c = null;
            try {
                c = ReferenceSearcher.findPreviousProof(openProofs(), goal.node());
            } catch (Exception exception) {
                LOGGER.warn("error during reference search", exception);
            }
            if (c != null) {
                p.closeGoal(goal);
                goal.node().register(c, ClosedBy.class);
                c.proof().addProofDisposedListenerFirst(new CopyBeforeDisposeF(c.proof(), p));
                closed++;
            }
        }
        updateGUIState(p);
        if (closed > 0) {
            showInfoAlert("Successfully closed " + closed + " open goal(s) by cache. "
                + "Use 'Copy referenced proof steps here' on the cached goals to copy the "
                + "steps into this proof.");
        }
    }

    /**
     * The proofs to search in: the proofs tracked through the selection events (every proof
     * that was selected at least once — the FX load path selects each loaded proof, so this
     * covers the currently opened proofs in practice).
     * <p>
     * <b>KNOWN-SIMPLIFIED:</b> the Swing original feeds {@code mediator.getCurrentlyOpenedProofs()}
     * to the reference search (CloseByReference.java:73, CachingExtension.java:172); the FX
     * {@link KeYMediatorF} has no equivalent accessor, so the tracked proofs are used instead.
     *
     * @return the non-null proof list
     */
    private List<Proof> openProofs() {
        List<Proof> proofs = trackedProofsUnmodifiable();
        KeYMediatorF m = mediator;
        if (m != null) {
            Proof selected = m.getSelectedProof();
            if (selected != null && !proofs.contains(selected)) {
                proofs.add(selected);
            }
        }
        return proofs;
    }

    /**
     * @return a copy of the proofs currently tracked by this extension (the raw {@link Set}
     *         snapshot used by {@link CachingPruneHandlerF} — no locking needed here because the
     *         caller iterates the copy).
     */
    List<Proof> trackedProofsUnmodifiable() {
        synchronized (trackedProofs) {
            return new ArrayList<>(trackedProofs);
        }
    }

    /** Shows an information dialog owned by the main window (message-dialog port). */
    private void showInfoAlert(String message) {
        Alert alert = new Alert(AlertType.INFORMATION, message, ButtonType.OK);
        alert.setTitle("Proof Caching");
        alert.setHeaderText(null);
        MainWindowF owner = window;
        if (owner != null) {
            alert.initOwner(owner.getStage());
        }
        alert.showAndWait();
    }
}
