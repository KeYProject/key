package de.uka.ilkd.key.gui.plugins.caching;

import java.awt.event.ActionEvent;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import javax.annotation.Nonnull;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.RuleAppListener;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.proof.io.IntermediateProofReplayer;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.proof.reference.CopyStepsAction;
import de.uka.ilkd.key.proof.reference.ReferenceSearcher;
import de.uka.ilkd.key.proof.replay.CopyingProofReplayer;

import org.key_project.util.collection.ImmutableList;

@KeYGuiExtension.Info(name = "Proof Caching", optional = true,
    description = "Functionality related to reusing previous proof results in similar proofs",
    experimental = false)
public class CloseReferenceExtension
        implements KeYGuiExtension, KeYGuiExtension.Startup, KeYGuiExtension.ContextMenu,
        KeYGuiExtension.Toolbar, KeYGuiExtension.StatusLine, KeYGuiExtension.Settings,
        KeYSelectionListener, RuleAppListener,
        ProofDisposedListener {

    private KeYMediator mediator;

    private final Set<Proof> trackedProofs = new HashSet<>();

    private static boolean ignoreRuleApplications = false;

    public static void setIgnoreRuleApplications(boolean ignoreRuleApplications) {
        CloseReferenceExtension.ignoreRuleApplications = ignoreRuleApplications;
    }

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
        if (e.getSource().lookup(CopyingProofReplayer.class) != null) {
            return; // copy in progress!
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
                        .addProofDisposedListener(new CopyBeforeDispose(mediator, c.getProof(), p));
            }
        }
    }

    @Override
    public void preInit(MainWindow window, KeYMediator mediator) {
        this.mediator = mediator;
        mediator.addKeYSelectionListener(this);
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
            return List.of(new CloseByReference(mediator, (Node) underlyingObject),
                new CopyReferencedProof(mediator, (Node) underlyingObject),
                new GotoReferencedProof(mediator, (Node) underlyingObject));
        }
        return new ArrayList<>();
    }

    @Nonnull
    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        JToolBar bar = new JToolBar();
        bar.add(new CopyStepsAction(mainWindow));
        return bar;
    }

    @Override
    public List<JComponent> getStatusLineComponents() {
        return List.of(new ReferenceSearchButton(mediator));
    }

    /**
     * Listener that ensures steps are copied before the referenced proof is disposed.
     */
    public static class CopyBeforeDispose implements ProofDisposedListener {

        private final KeYMediator mediator;
        private final Proof referencedProof;
        private final Proof newProof;

        /**
         * Construct new listener.
         *
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
            if (!newProof.isDisposed()) {
                mediator.stopInterface(true);
                newProof.copyCachedGoals(referencedProof);
                mediator.startInterface(true);
            }
        }

        @Override
        public void proofDisposed(ProofDisposedEvent e) {

        }
    }

    static class CloseByReference extends KeyAction {
        private final KeYMediator mediator;
        private final Node node;

        public CloseByReference(KeYMediator mediator, Node node) {
            this.mediator = mediator;
            this.node = node;
            setName("Close by reference to other proof");
            setEnabled(node.leaf() && !node.isClosed());
            setMenuPath("Proof Caching");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            // search other proofs for matching nodes
            ClosedBy c = ReferenceSearcher.findPreviousProof(
                mediator.getCurrentlyOpenedProofs(), node);
            if (c != null) {
                Node toClose = node;
                Proof newProof = node.proof();
                // newProof.closeGoal(newProof.getGoal(toClose));
                toClose.register(c, ClosedBy.class);
            } else {
                JOptionPane.showMessageDialog((JComponent) e.getSource(),
                    "No matching branch found", "Proof Caching error", JOptionPane.WARNING_MESSAGE);
            }
        }
    }

    static class CopyReferencedProof extends KeyAction {
        private final Node node;

        public CopyReferencedProof(KeYMediator mediator, Node node) {
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
                new CopyingProofReplayer(c.getProof(), node.proof()).copy(c.getNode(), current);
            } catch (IntermediateProofReplayer.BuiltInConstructionException ex) {
                throw new RuntimeException(ex);
            }
        }
    }

    static class GotoReferencedProof extends KeyAction {
        private final KeYMediator mediator;
        private final Node node;

        public GotoReferencedProof(KeYMediator mediator, Node node) {
            this.mediator = mediator;
            this.node = node;
            setName("Go to referenced proof");
            setEnabled(node.leaf() && !node.isClosed()
                    && node.lookup(ClosedBy.class) != null);
            setMenuPath("Proof Caching");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            ClosedBy c = node.lookup(ClosedBy.class);
            mediator.getSelectionModel().setSelectedNode(c.getNode());
        }
    }

    @Override
    public SettingsProvider getSettings() {
        return new CachingSettingsProvider();
    }
}
