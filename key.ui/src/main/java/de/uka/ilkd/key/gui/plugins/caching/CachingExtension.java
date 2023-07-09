package de.uka.ilkd.key.gui.plugins.caching;

import java.awt.event.ActionEvent;
import java.io.IOException;
import java.util.ArrayList;
import java.util.EventObject;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import javax.annotation.Nonnull;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.GUIListener;
import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.actions.ShowProofStatistics;
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
import de.uka.ilkd.key.proof.io.IntermediateProofReplayer;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.proof.reference.ReferenceSearcher;
import de.uka.ilkd.key.proof.replay.CopyingProofReplayer;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;

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
        KeYGuiExtension.StatusLine, KeYGuiExtension.Settings, GUIListener,
        KeYSelectionListener, RuleAppListener, ProofDisposedListener, ProverTaskListener {

    /**
     * Whether to enable the caching database. Remove (or replace with an optino) once the feature
     * is done.
     */
    public static final boolean ENABLE_DATABASE = false;
    private static final Logger LOGGER = LoggerFactory.getLogger(CachingExtension.class);

    /**
     * The mediator.
     */
    private KeYMediator mediator;

    /**
     * Proofs tracked for automatic reference search.
     */
    private final Set<Proof> trackedProofs = new HashSet<>();

    @Override
    public void selectedNodeChanged(KeYSelectionEvent e) {
    }

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
        if (e.getSource().lookup(CopyingProofReplayer.class) != null
                || e.getSource().lookup(TryCloseMacro.class) != null) {
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
                // p.closeGoal(goal);
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
        mediator.addGUIListener(this);
        mediator.getUI().addProverTaskListener(this);
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {

    }

    @Override
    public void shutDown(EventObject e) {
        CachingDatabase.shutdown();
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
        } else if (kind.getType() == Proof.class && ENABLE_DATABASE) {
            return List.of(new AddToDatabaseAction((Proof) underlyingObject));
        }
        return new ArrayList<>();
    }

    @Override
    public List<JComponent> getStatusLineComponents() {
        return List.of(new ReferenceSearchButton(mediator));
    }

    @Override
    public void taskStarted(TaskStartedInfo info) {

    }

    @Override
    public void taskProgress(int position) {

    }

    @Override
    public void taskFinished(TaskFinishedInfo info) {
        Proof p = info.getProof();
        if (p == null || p.closed() || !(info.getSource() instanceof ApplyStrategy
                || info.getSource() instanceof ProofMacro)) {
            return;
        }
        // show statistics if closed by reference
        if (p.countNodes() > 1 && p.openGoals().stream()
                .allMatch(goal -> goal.node().lookup(ClosedBy.class) != null)) {
            SwingUtilities.invokeLater(() -> {
                ShowProofStatistics.Window win =
                    new ShowProofStatistics.Window(MainWindow.getInstance(), p);
                win.setVisible(true);
            });
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
                    .equals(CachingSettingsProvider.DISPOSE_COPY)) {
                mediator.stopInterface(true);
                newProof.copyCachedGoals(referencedProof, null, null);
                mediator.startInterface(true);
            } else {
                newProof.openGoals().stream()
                        .filter(x -> x.node().lookup(ClosedBy.class) != null
                                && x.node().lookup(ClosedBy.class).getProof() == referencedProof)
                        .forEach(x -> {
                            x.setEnabled(true);
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
    static class AddToDatabaseAction extends KeyAction {
        /**
         * The node to try to close by reference.
         */
        private final Proof proof;

        /**
         * Construct new action.
         *
         * @param proof the proof
         */
        public AddToDatabaseAction(Proof proof) {
            this.proof = proof;
            setName("Add to database of cached proofs");
            setEnabled(proof.closed());
            setMenuPath("Proof Caching");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            try {
                CachingDatabase.addProof(proof);
            } catch (IOException err) {
                LOGGER.error("failed to add proof to database ", err);
                IssueDialog.showExceptionDialog(MainWindow.getInstance(), err);
            }
        }
    }

    /**
     * Action to search for suitable references on a single node.
     *
     * @author Arne Keller
     */
    static class CloseByReference extends KeyAction {
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
            setEnabled(node.leaf() && !node.isClosed() && node.lookup(ClosedBy.class) == null);
            setMenuPath("Proof Caching");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            // search other proofs for matching nodes
            ClosedBy c = ReferenceSearcher.findPreviousProof(
                mediator.getCurrentlyOpenedProofs(), node);
            if (c != null) {
                node.register(c, ClosedBy.class);
            } else {
                JOptionPane.showMessageDialog((JComponent) e.getSource(),
                    "No matching branch found", "Proof Caching error", JOptionPane.WARNING_MESSAGE);
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
            setEnabled(node.leaf() && !node.isClosed()
                    && node.lookup(ClosedBy.class) != null);
            setMenuPath("Proof Caching");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            ClosedBy c = node.lookup(ClosedBy.class);
            Goal current = node.proof().getGoal(node);
            try {
                mediator.stopInterface(true);
                new CopyingProofReplayer(c.getProof(), node.proof()).copy(c.getNode(), current);
                mediator.startInterface(true);
            } catch (IntermediateProofReplayer.BuiltInConstructionException ex) {
                throw new RuntimeException(ex);
            }
        }
    }

    @Override
    public SettingsProvider getSettings() {
        return new CachingSettingsProvider();
    }

    @Override
    public void modalDialogOpened(EventObject e) {

    }

    @Override
    public void modalDialogClosed(EventObject e) {

    }
}
