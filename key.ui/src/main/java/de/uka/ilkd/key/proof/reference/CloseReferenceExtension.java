package de.uka.ilkd.key.proof.reference;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.RuleAppListener;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.key_project.util.collection.ImmutableList;

@KeYGuiExtension.Info(name = "Proof Caching", optional = true,
    description = "Functionality related to reusing previous proof results in similar proofs",
    experimental = false)
public class CloseReferenceExtension
        implements KeYGuiExtension, KeYGuiExtension.Startup, KeYSelectionListener, RuleAppListener {

    private KeYMediator mediator;

    @Override
    public void selectedNodeChanged(KeYSelectionEvent e) {
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent e) {
        Proof p = e.getSource().getSelectedProof();
        if (p == null) {
            return;
        }
        p.addRuleAppListener(this);
    }

    @Override
    public void ruleApplied(ProofEvent e) {
        if (!ProofIndependentSettings.DEFAULT_INSTANCE.getProofCachingSettings().getEnabled()) {
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
                p.closeGoal(goal);
                goal.node().register(c, ClosedBy.class);
                c.getProof().addProofDisposedListener(new CopyBeforeDispose(c.getProof(), p));
            }
        }
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        this.mediator = mediator;
        mediator.addKeYSelectionListener(this);
    }

    /**
     * Listener that ensures steps are copied before the referenced proof is disposed.
     */
    private static class CopyBeforeDispose implements ProofDisposedListener {

        private final Proof referencedProof;
        private final Proof newProof;

        /**
         * Construct new listener.
         *
         * @param referencedProof referenced proof
         * @param newProof new proof
         */
        CopyBeforeDispose(Proof referencedProof, Proof newProof) {
            this.referencedProof = referencedProof;
            this.newProof = newProof;
        }

        @Override
        public void proofDisposing(ProofDisposedEvent e) {
            if (!newProof.isDisposed()) {
                newProof.copyCachedGoals(referencedProof);
            }
        }

        @Override
        public void proofDisposed(ProofDisposedEvent e) {

        }
    }
}
