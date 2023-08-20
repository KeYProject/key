/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import javax.annotation.Nonnull;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.ContextMenuAdapter;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;

import org.key_project.slicing.graph.GraphNode;
import org.key_project.slicing.ui.ShowCreatedByAction;
import org.key_project.slicing.ui.ShowGraphAction;
import org.key_project.slicing.ui.SlicingLeftPanel;

/**
 * Proof slicing extension.
 * For more details see <a href="https://keyproject.github.io/key-docs/user/ProofSlicing/">the user
 * guide</a>.
 *
 * @author Arne Keller
 */
@KeYGuiExtension.Info(name = "Slicing",
    description = "Author: Arne Keller <arne.keller@posteo.de>",
    experimental = false,
    optional = true,
    priority = 9001)
public class SlicingExtension implements KeYGuiExtension,
        KeYGuiExtension.ContextMenu,
        KeYGuiExtension.Startup,
        KeYGuiExtension.LeftPanel,
        KeYGuiExtension.Settings,
        KeYSelectionListener,
        ProofDisposedListener {
    /**
     * Collection of dependency trackers attached to proofs.
     */
    public final Map<Proof, DependencyTracker> trackers = new IdentityHashMap<>();
    /**
     * The left panel inserted into the GUI.
     */
    private SlicingLeftPanel leftPanel = null;
    /**
     * If set to true, the rule application de-duplication algorithm is automatically limited to
     * the "safe mode" for the next loaded proof.
     */
    private boolean enableSafeModeForNextProof = false;

    /**
     * The context menu adapter used by the extension.
     */
    private final ContextMenuAdapter adapter = new ContextMenuAdapter() {
        @Override
        public List<Action> getContextActions(
                KeYMediator mediator, ContextMenuKind kind, PosInSequent pos) {

            DependencyTracker tracker = trackers.get(mediator.getSelectedProof());
            if (tracker == null
                    || pos == null
                    || pos.getPosInOccurrence() == null
                    || pos.getPosInOccurrence().topLevel() == null
                    || mediator.getSelectedNode() == null) {
                return List.of();
            }
            Node currentNode = mediator.getSelectedNode();
            Proof currentProof = currentNode.proof();

            PosInOccurrence topLevel = pos.getPosInOccurrence().topLevel();
            Node node = tracker.getNodeThatProduced(currentNode, topLevel);
            if (node == null) {
                return List.of();
            }
            List<Action> list = new ArrayList<>();
            list.add(new ShowCreatedByAction(MainWindow.getInstance(), node));
            GraphNode graphNode = tracker.getDependencyGraph()
                    .getGraphNode(currentProof, currentNode.getBranchLocation(), topLevel);
            if (graphNode != null) {
                list.add(new ShowGraphAction(MainWindow.getInstance(), tracker, graphNode));
                // debugging dialog:
                // list.add(new ShowNodeInfoAction(MainWindow.getInstance(), tracker, graphNode));
            }
            return list;
        }
    };

    @Nonnull
    @Override
    public List<Action> getContextActions(@Nonnull KeYMediator mediator,
            @Nonnull ContextMenuKind kind,
            @Nonnull Object underlyingObject) {
        return adapter.getContextActions(mediator, kind, underlyingObject);
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent e) {
        createTrackerForProof(e.getSource().getSelectedProof());
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        mediator.addKeYSelectionListener(this);
        mediator.registerProofLoadListener(this::createTrackerForProof);
    }

    private void createTrackerForProof(Proof newProof) {
        trackers.computeIfAbsent(newProof, proof -> {
            if (proof == null) {
                return null;
            }
            proof.addProofDisposedListener(this);
            DependencyTracker tracker = new DependencyTracker(proof);
            if (leftPanel != null) {
                proof.addRuleAppListener(e -> leftPanel.ruleAppliedOnProof(proof, tracker));
                proof.addProofTreeListener(leftPanel);
                if (enableSafeModeForNextProof) {
                    SlicingSettingsProvider.getSlicingSettings()
                            .deactivateAggressiveDeduplicate(proof);
                    enableSafeModeForNextProof = false;
                }
            }
            return tracker;
        });
    }

    @Nonnull
    @Override
    public Collection<TabPanel> getPanels(
            @Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        if (leftPanel == null) {
            leftPanel = new SlicingLeftPanel(mediator, this);
            mediator.addKeYSelectionListener(leftPanel);
        }
        return Collections.singleton(leftPanel);
    }

    @Override
    public void proofDisposing(ProofDisposedEvent e) {
        trackers.put(e.getSource(), null);
        trackers.remove(e.getSource());
        if (leftPanel != null) {
            leftPanel.proofDisposed(e.getSource());
        }
    }

    @Override
    public void proofDisposed(ProofDisposedEvent e) {

    }

    @Override
    public SettingsProvider getSettings() {
        return new SlicingSettingsProvider();
    }

    /**
     * Activate the de-duplication safe mode for the next loaded proof.
     */
    public void enableSafeModeForNextProof() {
        this.enableSafeModeForNextProof = true;
    }
}
