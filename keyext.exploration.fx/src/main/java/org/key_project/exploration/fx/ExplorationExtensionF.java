/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.exploration.fx;

import java.util.ArrayList;
import java.util.List;
import javafx.scene.control.CheckBox;
import javafx.scene.control.CheckMenuItem;
import javafx.scene.control.Control;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.Tab;
import javafx.scene.control.Tooltip;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

import org.key_project.exploration.ExplorationModeModel;
import org.key_project.exploration.ExplorationNodeData;
import org.key_project.util.javafx.FxUtil;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * JavaFX port of the proof-exploration extension, MP9.2 counter-part of {@code
 * org.key_project.exploration.ExplorationExtension} (Swing ExplorationExtension.java:46-174).
 * <p>
 * The extension lets the user annotate a proof with "exploration" steps: formulas are added to /
 * edited / hidden in the sequent via the {@code ProofExplorationService} (reused unmodified from
 * the Swing module), the performed actions are tracked per node ({@link ExplorationNodeData}),
 * and the mode is toggled from the toolbar, a "Exploration" menu and — like the Swing original —
 * from the sequent context menu. The example provider pattern follows the built-in
 * {@code de.uka.ilkd.key.gui.fx.extension.contrib} providers of {@code key.ui.fx}.
 * <p>
 * <b>KNOWN-SIMPLIFIED</b> decisions of this port (each marked at the respective site):
 * <ul>
 * <li>The Swing provider registers the {@link ExplorationModeModel} into the Swing mediator
 * ({@code mediator.register(model, ExplorationModeModel.class)}) and the {@code
 * ExplorationRenderer} (a purple border/background on exploration nodes) into the Swing proof
 * tree. {@code KeYMediatorF} has no register/lookup seam and the FX {@code ProofTreeViewF} has no
 * renderer styling hook — both are dropped; the model is held directly by this provider.</li>
 * <li>The "Hide justification" toggle persists the {@code ViewSettings.hideInteractiveGoals}
 * flag and the exploration taclet-application state like the Swing
 * {@code ShowInteractiveBranchesAction}, but the actual proof-tree filter of the Swing original
 * ({@code ExplorationModeModel.setShowInteractiveBranches} → Swing
 * {@code GUIProofTreeModel.setFilter(HIDE_INTERACTIVE_GOALS, …)}) targets a Swing proof-tree seam
 * that does not exist in {@code key.ui.fx} (the filter is explicitly deferred there).</li>
 * <li>Icons: the Swing {@code Icons} class is AWT/Swing-bound — plain unicode markers are used
 * instead.</li>
 * </ul>
 */
@NullMarked
@KeYGuiExtensionF.Info(name = "Exploration",
    description = "Author: Sarah Grebing <grebing@ira.uka.de>, Alexander Weigl "
        + "<weigl@ira.uka.de> — JavaFX port (MP9.2). Add, edit and hide formulas on the "
        + "sequent with sound-cut based exploration steps and collect them in the "
        + "'Exploration Steps' panel. KNOWN-SIMPLIFIED: proof-tree styling and the hidden "
        + "second-branch filter are deferred (no FX seam).",
    experimental = true, optional = true, priority = 10000)
public class ExplorationExtensionF implements KeYGuiExtensionF, KeYGuiExtensionF.ToolbarF,
        KeYGuiExtensionF.MainMenuF, KeYGuiExtensionF.StatusLineF, KeYGuiExtensionF.LeftPanelF,
        KeYGuiExtensionF.ContextMenuF, KeYGuiExtensionF.StartupF, ProofDisposedListener {

    /** the shared exploration model, held by this provider (see class javadoc). */
    private final ExplorationModeModel model = new ExplorationModeModel();

    /** the lazily-built exploration steps panel (west-drawer tab + status-line indicator). */
    private @Nullable ExplorationStepsPanelF leftPanel;

    /** the window and mediator of the running app; wired in {@link #init}, nullable in tests. */
    private @Nullable MainWindowF window;
    private @Nullable KeYMediatorF mediator;

    /** the cached toolbar/menu toggle views, kept in sync with the model by the listener below. */
    private @Nullable CheckBox exploreModeCheck;
    private @Nullable CheckBox hideJustificationCheck;
    private final List<CheckBox> exploreModeChecks = new ArrayList<>();
    private final List<CheckMenuItem> exploreModeMenuItems = new ArrayList<>();
    private final List<CheckBox> hideJustificationChecks = new ArrayList<>();
    private final List<CheckMenuItem> hideJustificationMenuItems = new ArrayList<>();

    /**
     * The proof-tree listener that cleans up the exploration annotation of a pruned subtree
     * (Swing ExplorationExtension.proofTreeListener, ExplorationExtension.java:75-82).
     */
    private final ProofTreeListener proofTreeListener = new ProofTreeAdapter() {
        @Override
        public void proofPruned(ProofTreeEvent e) {
            Node node = e.getNode();
            if (node == null) {
                return;
            }
            @Nullable
            ExplorationNodeData data = node.lookup(ExplorationNodeData.class);
            if (data != null) {
                node.deregister(data, ExplorationNodeData.class);
            }
        }
    };

    public ExplorationExtensionF() {
        // Keep every toggle view (toolbar checkboxes + menu check items) and the left-panel
        // enablement in sync with the model; the event may arrive from the prover thread, so the
        // update is marshalled to the FX thread (guarded, the listener also fires while the
        // toolkit is only just starting).
        model.addPropertyChangeListener(ExplorationModeModel.PROP_EXPLORE_MODE,
            e -> FxUtil.runLater(this::syncExplorationModeUi));
    }

    // ------------------------------------------------------------------
    // ToolbarF — the Swing JToolBar with the two JCheckBoxes
    // (ExplorationExtension.java:91-99) as FX controls
    // ------------------------------------------------------------------

    @Override
    public List<Control> getToolbarControls(@Nullable MainWindowF window,
            @Nullable KeYMediatorF mediator) {
        // Swing ExplorationExtension.getToolbar: toggle + show-interactive-branches checkbox,
        // both wired to the same model-backed actions the menu uses.
        return List.of(getExploreModeToggle(), getHideJustificationToggle());
    }

    private CheckBox getExploreModeToggle() {
        if (exploreModeCheck == null) {
            CheckBox check = new CheckBox("Exploration Mode");
            check.setTooltip(new Tooltip("Choose to start ExplorationMode"));
            check.setSelected(model.isExplorationModeSelected());
            check.setOnAction(e -> model.setExplorationModeSelected(check.isSelected()));
            exploreModeCheck = check;
            exploreModeChecks.add(check);
        }
        return exploreModeCheck;
    }

    private CheckBox getHideJustificationToggle() {
        if (hideJustificationCheck == null) {
            CheckBox check = new CheckBox("Hide justification");
            check.setTooltip(new Tooltip("""
                    Exploration actions are often done using a cut. \
                    Choose to hide the second cut-branches from the view to focus on the \
                    actions. Uncheck to focus on these branches."""));
            check.setSelected(!model.isShowInteractiveBranches());
            check.setDisable(!model.isExplorationModeSelected());
            check.setOnAction(e -> setHideJustification(check.isSelected()));
            hideJustificationCheck = check;
            hideJustificationChecks.add(check);
        }
        return hideJustificationCheck;
    }

    // ------------------------------------------------------------------
    // MainMenuF — the Swing getMainMenuActions (ToggleExplorationAction +
    // ShowInteractiveBranchesAction, ExplorationExtension.java:157-161) as one FX menu
    // ------------------------------------------------------------------

    @Override
    public List<Menu> getMenus(@Nullable MainWindowF window, @Nullable KeYMediatorF mediator) {
        // The Swing original groups its exploration actions into the View menu; the FX SPI
        // contributes whole new menus, so the two toggles live in a new "Exploration" menu (the
        // five built-in menus stay untouched — key.fx.verify.menuparity keeps asserting
        // 16/24/12/7/5).
        Menu menu = new Menu("Exploration");
        menu.getItems().addAll(getExploreModeMenuItem(), getHideJustificationMenuItem());
        return List.of(menu);
    }

    private MenuItem getExploreModeMenuItem() {
        CheckMenuItem item = new CheckMenuItem("Exploration Mode");
        item.setSelected(model.isExplorationModeSelected());
        item.setOnAction(e -> model.setExplorationModeSelected(item.isSelected()));
        exploreModeMenuItems.add(item);
        return item;
    }

    private MenuItem getHideJustificationMenuItem() {
        CheckMenuItem item = new CheckMenuItem("Hide justification");
        item.setSelected(!model.isShowInteractiveBranches());
        item.setDisable(!model.isExplorationModeSelected());
        item.setOnAction(e -> setHideJustification(item.isSelected()));
        hideJustificationMenuItems.add(item);
        return item;
    }

    // ------------------------------------------------------------------
    // StatusLineF — the Swing hasExplorationSteps JLabel
    // (ExplorationExtension.java:148-155) as an FX label of the steps panel
    // ------------------------------------------------------------------

    @Override
    public List<Control> getStatusLineControls() {
        // Swing returns leftPanel.getHasExplorationSteps(): a singleton indicator refreshed by
        // the panel model. The same label object is exposed by the FX panel.
        return List.of(getLeftPanel().getHasExplorationSteps());
    }

    // ------------------------------------------------------------------
    // LeftPanelF — the Swing ExplorationStepsList TabPanel
    // (ExplorationExtension.java:131-146) as a west-drawer FX tab
    // ------------------------------------------------------------------

    @Override
    public List<Tab> getLeftPanelTabs(@Nullable MainWindowF window,
            @Nullable KeYMediatorF mediator) {
        // MP10: the host registers extension left-panel tabs as west-drawer items
        // (MainWindowF.buildDrawerHosts), exactly one tab like the Swing singleton panel.
        ExplorationStepsPanelF panel = getLeftPanel();
        Tab tab = new Tab(panel.getTitle(), panel);
        tab.setClosable(false);
        return List.of(tab);
    }

    private ExplorationStepsPanelF getLeftPanel() {
        // lazy singleton like the Swing provider's initLeftPanel (ExplorationExtension.java:131)
        if (leftPanel == null) {
            leftPanel = new ExplorationStepsPanelF(window, mediator);
            leftPanel.setEnabled(model.isExplorationModeSelected());
        }
        return leftPanel;
    }

    // ------------------------------------------------------------------
    // ContextMenuF — the Swing ContextMenuAdapter for ContextMenuKind.SEQUENT_VIEW
    // (ExplorationExtension.java:59-73): add-to-antecedent / add-to-succedent / edit / delete
    // ------------------------------------------------------------------

    @Override
    public List<MenuItem> getSequentContextItems(@Nullable KeYMediatorF mediator,
            @Nullable Goal goal, @Nullable PosInSequent pos) {
        // The Swing adapter contributes nothing unless the exploration mode is selected and the
        // clicked kind is SEQUENT_VIEW; the FX SPI exposes exactly that slot. Guards against
        // nulls: the term-menu self tests exercise the facade headless without goal/position.
        if (!model.isExplorationModeSelected() || mediator == null || goal == null
                || pos == null) {
            return List.of();
        }
        return ExplorationSequentMenuF.items(mediator, goal, pos);
    }

    // ------------------------------------------------------------------
    // StartupF — Swing ExplorationExtension.init (ExplorationExtension.java:101-129):
    // model binding, selection listener (proof swap + listener registration) and the
    // proof-disposed hookup — FX-safe
    // ------------------------------------------------------------------

    @Override
    public void init(@Nullable MainWindowF window, @Nullable KeYMediatorF mediator) {
        if (window != null) {
            this.window = window;
        }
        if (mediator == null) {
            // startup hook without a mediator (headless runs): nothing to wire
            return;
        }
        this.mediator = mediator;
        // KNOWN-SIMPLIFIED: the Swing original registers the model in the mediator registry
        // (mediator.register(model, ExplorationModeModel.class)); KeYMediatorF has no
        // register/lookup seam, so the FX provider holds the singleton model directly — no
        // consumer of the Swing registration exists in the FX UI.
        ExplorationStepsPanelF panel = getLeftPanel();
        // the host builds status bar/drawer hosts during window construction, before this init
        // hook — re-seed the panel with the real window/mediator references
        panel.wire(window, mediator);
        panel.setEnabled(model.isExplorationModeSelected());
        mediator.getSelectionModel().addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
                // selection events may fire from the prover thread → marshal to the FX thread
                FxUtil.runLater(() -> onSelectedProofChanged(mediator, panel));
            }
        });
    }

    private void onSelectedProofChanged(KeYMediatorF mediator, ExplorationStepsPanelF panel) {
        // Swing ExplorationExtension.init:109-125 — swap the panel's proof and move the
        // proof-tree and proof-disposed listeners to the newly selected proof.
        Proof oldProof = panel.getProof();
        Proof newProof = mediator.getSelectedProof();
        if (oldProof != newProof) {
            panel.setProof(newProof);
            if (oldProof != null) {
                oldProof.removeProofTreeListener(proofTreeListener);
            }
            if (newProof != null) {
                newProof.addProofTreeListener(proofTreeListener);
                newProof.addProofDisposedListener(this);
            }
        }
    }

    // ------------------------------------------------------------------
    // ProofDisposedListener — Swing ExplorationExtension.proofDisposing
    // (ExplorationExtension.java:163-168)
    // ------------------------------------------------------------------

    @Override
    public void proofDisposing(ProofDisposedEvent e) {
        ExplorationStepsPanelF panel = leftPanel;
        if (panel != null && e.getSource() == panel.getProof()) {
            FxUtil.runLater(() -> panel.setProof(null));
        }
    }

    @Override
    public void proofDisposed(ProofDisposedEvent e) {
        // empty like the Swing original
    }

    // ------------------------------------------------------------------
    // model ↔ UI wiring
    // ------------------------------------------------------------------

    private void syncExplorationModeUi() {
        boolean selected = model.isExplorationModeSelected();
        exploreModeChecks.forEach(c -> c.setSelected(selected));
        exploreModeMenuItems.forEach(c -> c.setSelected(selected));
        // the hide-justification toggles re-read the persisted ViewSettings flag on every mode
        // change, like Swing ShowInteractiveBranchesAction.updateEnable (ShowInteractiveBranches
        // Action.java:42-53), and are only enabled while the exploration mode is active.
        boolean hide = !model.isShowInteractiveBranches();
        hideJustificationChecks.forEach(c -> {
            c.setSelected(hide);
            c.setDisable(!selected);
        });
        hideJustificationMenuItems.forEach(c -> {
            c.setSelected(hide);
            c.setDisable(!selected);
        });
        ExplorationStepsPanelF panel = leftPanel;
        if (panel != null) {
            panel.setEnabled(selected);
        }
    }

    /**
     * The "Hide justification" toggle, FX port of the Swing {@code
     * ShowInteractiveBranchesAction} (ShowInteractiveBranchesAction.java:21-69).
     * <p>
     * KNOWN-SIMPLIFIED: the Swing action routes through
     * {@code ExplorationModeModel.setShowInteractiveBranches}, which calls
     * {@code MainWindow.getProofTreeView().getDelegateModel().setFilter(HIDE_INTERACTIVE_GOALS,
     * …)} — a Swing proof-tree seam that does not exist in {@code key.ui.fx} (the FX
     * {@code ProofTreeViewF} explicitly defers that filter). The FX port persists the same
     * {@link ViewSettings#setHideInteractiveGoals(boolean)} flag the Swing filter reads and
     * records the exploration-app state; the filter itself stays deferred.
     */
    private void setHideJustification(boolean hide) {
        ViewSettings viewSettings = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        viewSettings.setHideInteractiveGoals(hide);
        model.setExplorationTacletAppState(
            hide ? ExplorationModeModel.ExplorationState.SIMPLIFIED_APP
                    : ExplorationModeModel.ExplorationState.WHOLE_APP);
    }
}
