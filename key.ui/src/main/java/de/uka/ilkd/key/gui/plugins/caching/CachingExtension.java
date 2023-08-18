/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

import java.awt.event.ActionEvent;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import javax.annotation.Nonnull;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.TryCloseMacro;
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
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.settings.ProofCachingSettings;

import org.key_project.util.collection.ImmutableList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Extension for proof caching.
 *
 * @author Arne Keller
 */
@KeYGuiExtension.Info(name = "Proof Caching", optional = true,
    description = "Functionality related to reusing previous proof results in similar proofs",
    experimental = false)
public class CachingExtension
        implements KeYGuiExtension, KeYGuiExtension.Startup, KeYGuiExtension.ContextMenu,
        KeYGuiExtension.StatusLine, KeYGuiExtension.Settings,
        KeYSelectionListener, RuleAppListener, ProofDisposedListener, ProverTaskListener {
    private static final Logger LOGGER = LoggerFactory.getLogger(CachingExtension.class);

    /**
     * The mediator.
     */
    private KeYMediator mediator;
    /**
     * Whether to try to close the current proof after a rule application.
     * Will be false when running certain macros.
     */
    private boolean tryToClose = false;

    /**
     * Proofs tracked for automatic reference search.
     */
    private final Set<Proof> trackedProofs = new HashSet<>();
    private ReferenceSearchButton referenceSearchButton;

    @Override
    public void selectedProofChanged(KeYSelectionEvent e) {
        Proof p = e.getSource().getSelectedProof();
        if (p == null || trackedProofs.contains(p)) {
            return;
        }
        trackedProofs.add(p);
        p.addRuleAppListener(this);
        p.addProofDisposedListener(this);
    }

    @Override
    public void ruleApplied(ProofEvent e) {
        if (!tryToClose) {
            return;
        }
        if (e.getSource().lookup(CopyingProofReplayer.class) != null) {
            // either:
            // copy in progress,
            // macro that excepts the proof to really close in progress
            return;
        }
        if (!CachingSettingsProvider.getCachingSettings().getEnabled()) {
            return;
        }
        Proof p = e.getSource();
        if (e.getRuleAppInfo().getOriginalNode().getNodeInfo().getInteractiveRuleApplication()) {
            return; // only applies for automatic proof search
        }
        ImmutableList<Goal> newGoals = e.getNewGoals();
        if (newGoals.size() <= 1) {
            return;
        }
        for (Goal goal : newGoals) {
            ClosedBy c = ReferenceSearcher.findPreviousProof(mediator.getCurrentlyOpenedProofs(),
                goal.node());
            if (c != null) {
                goal.setEnabled(false);

                goal.node().register(c, ClosedBy.class);
                c.getProof()
                        .addProofDisposedListenerFirst(
                            new CopyBeforeDispose(mediator, c.getProof(), p));
            }
        }
    }

    @Override
    public void preInit(MainWindow window, KeYMediator mediator) {
        this.mediator = mediator;
        mediator.addKeYSelectionListener(this);
        mediator.getUI().addProverTaskListener(this);
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {

    }

    @Override
    public void proofDisposing(ProofDisposedEvent e) {
        trackedProofs.remove(e.getSource());
    }

    @Override
    public void proofDisposed(ProofDisposedEvent e) {

    }

    @Nonnull
    @Override
    public List<Action> getContextActions(@Nonnull KeYMediator mediator,
            @Nonnull ContextMenuKind kind, @Nonnull Object underlyingObject) {
        if (kind.getType() == Node.class) {
            Node node = (Node) underlyingObject;
            List<Action> actions = new ArrayList<>();
            actions.add(new CloseByReference(mediator, node));
            actions.add(new CopyReferencedProof(mediator, node));
            actions.add(new GotoReferenceAction(mediator, node));
            return actions;
        }
        return new ArrayList<>();
    }

    @Override
    public List<JComponent> getStatusLineComponents() {
        referenceSearchButton = new ReferenceSearchButton(mediator);
        return List.of(referenceSearchButton);
    }

    @Override
    public void taskStarted(TaskStartedInfo info) {
        if (info.getKind().equals(TaskStartedInfo.TaskKind.Macro)
                && info.getMessage().equals(new TryCloseMacro().getName())) {
            tryToClose = false;
        }
    }

    @Override
    public void taskProgress(int position) {
        tryToClose = true;
    }

    @Override
    public void taskFinished(TaskFinishedInfo info) {
        tryToClose = info.getSource() instanceof TryCloseMacro;
        if (tryToClose) {
            return; // try close macro was running, no need to do anything here
        }
        Proof p = info.getProof();
        if (p == null || p.isDisposed() || p.closed() || !(info.getSource() instanceof ApplyStrategy
                || info.getSource() instanceof ProofMacro)) {
            return;
        }
        // unmark interactive goals
        if (p.countNodes() > 1 && p.openGoals().stream()
                .anyMatch(goal -> goal.node().lookup(ClosedBy.class) != null)) {
            // mark goals as automatic again
            p.openGoals().stream().filter(goal -> goal.node().lookup(ClosedBy.class) != null)
                    .forEach(g -> {
                        g.setEnabled(true);
                        g.proof().closeGoal(g);
                    });
            // statistics dialog is automatically shown
        }
    }

    /**
     * Listener that ensures steps are copied before the referenced proof is disposed.
     *
     * @author Arne Keller
     */
    public static class CopyBeforeDispose implements ProofDisposedListener {

        /**
         * The mediator.
         */
        private final KeYMediator mediator;
        /**
         * The referenced proof.
         */
        private final Proof referencedProof;
        /**
         * The new proof.
         */
        private final Proof newProof;

        /**
         * Construct new listener.
         *
         * @param mediator the mediator
         * @param referencedProof referenced proof
         * @param newProof new proof
         */
        public CopyBeforeDispose(KeYMediator mediator, Proof referencedProof, Proof newProof) {
            this.mediator = mediator;
            this.referencedProof = referencedProof;
            this.newProof = newProof;
        }

        @Override
        public void proofDisposing(ProofDisposedEvent e) {
            if (newProof.isDisposed()) {
                return;
            }
            if (CachingSettingsProvider.getCachingSettings().getDispose()
                    .equals(ProofCachingSettings.DISPOSE_COPY)) {
                mediator.stopInterface(true);
                newProof.copyCachedGoals(referencedProof, null, null);
                mediator.startInterface(true);
            } else {
                newProof.closedGoals().stream()
                        .filter(x -> x.node().lookup(ClosedBy.class) != null
                                && x.node().lookup(ClosedBy.class).getProof() == referencedProof)
                        .forEach(x -> {
                            newProof.reOpenGoal(x);
                            x.node().deregister(x.node().lookup(ClosedBy.class), ClosedBy.class);
                        });
            }
        }

        @Override
        public void proofDisposed(ProofDisposedEvent e) {

        }
    }

    /**
     * Action to search for suitable references on a single node.
     *
     * @author Arne Keller
     */
    private final class CloseByReference extends KeyAction {
        /**
         * The mediator.
         */
        private final KeYMediator mediator;
        /**
         * The node to try to close by reference.
         */
        private final Node node;

        /**
         * Construct new action.
         *
         * @param mediator the mediator
         * @param node the node
         */
        public CloseByReference(KeYMediator mediator, Node node) {
            this.mediator = mediator;
            this.node = node;
            setName("Close by reference to other proof");
            setEnabled(!node.isClosed() && node.lookup(ClosedBy.class) == null);
            setMenuPath("Proof Caching");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            List<Node> nodes = new ArrayList<>();
            if (node.leaf()) {
                nodes.add(node);
            } else {
                node.subtreeIterator().forEachRemaining(n -> {
                    if (n.leaf() && !n.isClosed()) {
                        nodes.add(n);
                    }
                });
            }
            List<Integer> mismatches = new ArrayList<>();
            for (Node n : nodes) {
                // search other proofs for matching nodes
                ClosedBy c = ReferenceSearcher.findPreviousProof(
                    mediator.getCurrentlyOpenedProofs(), n);
                if (c != null) {
                    n.proof().closeGoal(n.proof().getOpenGoal(n));
                    n.register(c, ClosedBy.class);
                } else {
                    mismatches.add(n.serialNr());
                }
            }
            if (!nodes.isEmpty()) {
                referenceSearchButton.updateState(nodes.get(0).proof());
            }
            if (!mismatches.isEmpty()) {
                // since e.getSource() is the popup menu, it is better to use the MainWindow
                // instance here as a parent
                JOptionPane.showMessageDialog(MainWindow.getInstance(),
                    "No matching branch found for node(s) " + Arrays.toString(mismatches.toArray()),
                    "Proof Caching error", JOptionPane.WARNING_MESSAGE);
            }
        }
    }

    /**
     * Action to copy referenced proof steps to the new proof.
     *
     * @author Arne Keller
     */
    private static class CopyReferencedProof extends KeyAction {
        /**
         * The mediator.
         */
        private final KeYMediator mediator;
        /**
         * The node to copy the steps to.
         */
        private final Node node;

        /**
         * Construct a new action.
         *
         * @param mediator the mediator
         * @param node the node
         */
        public CopyReferencedProof(KeYMediator mediator, Node node) {
            this.mediator = mediator;
            this.node = node;
            setName("Copy referenced proof steps here");
            setEnabled(node.leaf() && node.isClosed()
                    && node.lookup(ClosedBy.class) != null);
            setMenuPath("Proof Caching");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            ClosedBy c = node.lookup(ClosedBy.class);
            Goal current = node.proof().getClosedGoal(node);
            try {
                mediator.stopInterface(true);
                new CopyingProofReplayer(c.getProof(), node.proof()).copy(c.getNode(), current);
                mediator.startInterface(true);
            } catch (Exception ex) {
                LOGGER.error("failed to copy proof ", ex);
                IssueDialog.showExceptionDialog(MainWindow.getInstance(), ex);
            }
        }
    }

    @Override
    public SettingsProvider getSettings() {
        return new CachingSettingsProvider();
    }
}
