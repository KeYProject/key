/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.slicing.fx;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import javafx.scene.control.MenuItem;
import javafx.scene.control.Tab;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.gui.fx.settings.SettingsProviderF;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.slicing.DependencyTracker;
import org.key_project.slicing.SlicingSettingsProvider;
import org.key_project.slicing.fx.ui.SlicingLeftPanelF;
import org.key_project.slicing.graph.GraphNode;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Proof slicing extension, FX port of {@code org.key_project.slicing.SlicingExtension} (the
 * Swing KeYGuiExtension provider, SlicingExtension.java:48-215). Registered via the service
 * loader and implements the same capability set: a left-panel tab (the {@link SlicingLeftPanelF},
 * west drawer item), the SEQUENT_VIEW context-menu items, the settings provider and the startup
 * hook (tracker creation + the single-core-only parallel-prover guard). The slicing logic itself
 * (the {@link DependencyTracker}, the dependency graph and the {@code SlicingProofReplayer}) is
 * reused unchanged from {@code keyext.slicing}.
 * <p>
 * <b>KNOWN-SIMPLIFIED:</b> the Swing provider additionally registers a proof-load listener
 * through the Swing mediator ({@code mediator.registerProofLoadListener}); the FX mediator has no
 * such registry, and every proof load routes through
 * {@code KeYSelectionModel.setSelectedProof} anyway, so the {@link KeYSelectionListener} below
 * covers both the "new proof loaded" and the "selected proof switched" cases.
 *
 * @author Alexander Weigl
 * @author Arne Keller (port)
 */
@KeYGuiExtensionF.Info(name = "Slicing",
    description = "Author: Arne Keller <arne.keller@posteo.de>",
    experimental = false,
    optional = true,
    priority = 9001)
@NullMarked
public class SlicingExtensionF implements KeYGuiExtensionF, KeYGuiExtensionF.ContextMenuF,
        KeYGuiExtensionF.StartupF, KeYGuiExtensionF.LeftPanelF, KeYGuiExtensionF.SettingsF,
        KeYSelectionListener, ProofDisposedListener {

    private static final Logger LOGGER = LoggerFactory.getLogger(SlicingExtensionF.class);

    /**
     * Collection of dependency trackers attached to proofs (Swing
     * {@code SlicingExtension.trackers}).
     */
    public final Map<Proof, DependencyTracker> trackers = new IdentityHashMap<>();

    /**
     * The left panel inserted into the west drawer, created lazily on the first
     * {@link #getLeftPanelTabs} call (Swing {@code SlicingExtension.leftPanel}).
     */
    private @Nullable SlicingLeftPanelF leftPanel = null;

    /**
     * The main window this extension is attached to; {@code null} until the provider is wired
     * into a window (never in the running app — the SPI callbacks always pass one — and in
     * unit tests).
     */
    private @Nullable MainWindowF window;

    /**
     * If set to true, the rule application de-duplication algorithm is automatically limited to
     * the "safe mode" for the next loaded proof (Swing {@code SlicingExtension.
     * enableSafeModeForNextProof}).
     */
    private boolean enableSafeModeForNextProof = false;

    /** Lazily created settings provider (Swing {@code SlicingSettingsProvider}). */
    private @Nullable SettingsProviderF settingsProvider = null;

    /**
     * @return the main window this extension is attached to, may be {@code null} in unit tests
     */
    @Nullable
    public MainWindowF window() {
        return window;
    }

    @Override
    public void init(MainWindowF window, KeYMediatorF mediator) {
        this.window = window;
        mediator.getSelectionModel().addKeYSelectionListener(this);
        // Slicing is single-core only (Swing SlicingExtension.init): enabling the multi-core
        // prover suspends every DependencyTracker for the duration of each run, so it silently
        // misses the rules that run applies. Mark all existing trackers incomplete the instant
        // the multi-core prover is switched on, so a later switch back to single-core can never
        // slice a proof from a graph with a gap in it. (New trackers are not created while the
        // multi-core prover is enabled; see createTrackerForProof.)
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().addPropertyChangeListener(
            GeneralSettings.PARALLEL_PROVER_ENABLED, evt -> {
                if (ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
                        .isParallelProverEnabled()) {
                    trackers.values().forEach(tracker -> {
                        if (tracker != null) {
                            tracker.markIncompleteAfterParallelRun();
                        }
                    });
                }
                SlicingLeftPanelF panel = leftPanel;
                if (panel != null) {
                    org.key_project.util.javafx.FxUtil.runLater(panel::updateUIState);
                }
            });
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
        createTrackerForProof(e.getSource().getSelectedProof());
    }

    /**
     * Attach a dependency tracker to the given proof (Swing
     * {@code SlicingExtension.createTrackerForProof}): skipped while the multi-core prover is
     * enabled (slicing is single-core only; the tracker would miss everything the parallel
     * prover applies).
     *
     * @param newProof the proof to attach a tracker to, may be {@code null}
     */
    private void createTrackerForProof(@Nullable Proof newProof) {
        if (newProof == null) {
            return;
        }
        // Proof slicing is a single-core-only feature: do not attach a tracker while the
        // multi-core prover is enabled.
        if (ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
                .isParallelProverEnabled()) {
            return;
        }
        trackers.computeIfAbsent(newProof, proof -> {
            proof.addProofDisposedListener(this);
            DependencyTracker tracker = new DependencyTracker(proof);
            SlicingLeftPanelF panel = leftPanel;
            if (panel != null) {
                proof.addRuleAppListener(e -> panel.ruleAppliedOnProof(proof, tracker));
                proof.addProofTreeListener(panel);
                if (enableSafeModeForNextProof) {
                    SlicingSettingsProvider.getSlicingSettings()
                            .deactivateAggressiveDeduplicate(proof);
                    enableSafeModeForNextProof = false;
                }
            }
            return tracker;
        });
    }

    /**
     * The left-panel singleton tab (created together with the panel on the first
     * {@link #getLeftPanelTabs} call); repeated queries return the same tab.
     */
    private @Nullable Tab leftPanelTab = null;

    @Override
    public List<Tab> getLeftPanelTabs(MainWindowF window, KeYMediatorF mediator) {
        if (leftPanel == null) {
            this.window = window;
            leftPanel = new SlicingLeftPanelF(mediator, this);
            mediator.getSelectionModel().addKeYSelectionListener(leftPanel);
            leftPanelTab = new Tab();
            leftPanelTab.setText(getPanelTitle());
            leftPanelTab.setClosable(false);
            leftPanelTab.setContent(leftPanel);
        }
        return List.of(leftPanelTab);
    }

    /**
     * @return the title of the left panel / west drawer item (Swing
     *         {@code SlicingLeftPanel.getTitle})
     */
    static String getPanelTitle() {
        return "Proof Slicing";
    }

    @Override
    public List<MenuItem> getSequentContextItems(KeYMediatorF mediator, Goal goal,
            PosInSequent pos) {
        // The guards of the Swing adapter (SlicingExtension.java:86-101): the items only make
        // sense if a tracker exists for the selected proof and the clicked position resolves to
        // a formula that some proof step produced.
        if (trackers.isEmpty() || pos == null || pos.getPosInOccurrence() == null
                || pos.getPosInOccurrence().topLevel() == null
                || mediator.getSelectedNode() == null) {
            return List.of();
        }
        DependencyTracker tracker = trackers.get(mediator.getSelectedProof());
        if (tracker == null) {
            return List.of();
        }
        Node currentNode = mediator.getSelectedNode();
        Proof currentProof = currentNode.proof();

        PosInOccurrence topLevel = pos.getPosInOccurrence().topLevel();
        Node node = tracker.getNodeThatProduced(currentNode, topLevel);
        if (node == null) {
            return List.of();
        }
        List<MenuItem> list = new ArrayList<>();
        list.add(showCreatedByItem(mediator, node));
        GraphNode graphNode = tracker.getDependencyGraph()
                .getGraphNode(currentProof, currentNode.getBranchLocation(), topLevel);
        if (graphNode != null) {
            list.add(showGraphItem(tracker, graphNode));
        }
        return list;
    }

    /**
     * The "Show proof step that created this formula" item (Swing {@code ShowCreatedByAction}):
     * switches the FX selection to the producing node.
     */
    private static MenuItem showCreatedByItem(KeYMediatorF mediator, Node node) {
        MenuItem item = new MenuItem(String.format(
            "Show proof step that created this formula (switches to proof step %d)",
            node.serialNr()));
        item.setOnAction(e -> mediator.getSelectionModel().setSelectedNode(node));
        return item;
    }

    /**
     * The "Show dependency graph around this formula" item (Swing {@code ShowGraphAction});
     * KNOWN-SIMPLIFIED: the Swing action renders the DOT excerpt through
     * {@code PreviewDialog}; this port shows the DOT source in a text dialog instead (the
     * graphviz image renderer is Swing-only).
     */
    private static MenuItem showGraphItem(DependencyTracker tracker, GraphNode graphNode) {
        MenuItem item = new MenuItem("Show dependency graph around this formula");
        item.setOnAction(e -> {
            String text = tracker.exportDotAround(false, false, graphNode);
            SlicingLeftPanelF.showTextDialog("Dependency graph around this formula", text);
        });
        return item;
    }

    @Override
    public SettingsProviderF getSettings() {
        if (settingsProvider == null) {
            settingsProvider = new SlicingSettingsProviderF();
        }
        return settingsProvider;
    }

    @Override
    public void proofDisposing(ProofDisposedEvent e) {
        trackers.put(e.getSource(), null);
        trackers.remove(e.getSource());
        SlicingLeftPanelF panel = leftPanel;
        if (panel != null) {
            panel.proofDisposed(e.getSource());
        }
    }

    @Override
    public void proofDisposed(ProofDisposedEvent e) {
        // mirror of the Swing provider: nothing to do on full disposal
    }

    /**
     * Activate the de-duplication safe mode for the next loaded proof (Swing
     * {@code SlicingExtension.enableSafeModeForNextProof}).
     */
    public void enableSafeModeForNextProof() {
        this.enableSafeModeForNextProof = true;
    }
}
