package de.uka.ilkd.key.proof.reference;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.RuleAppListener;
import org.key_project.util.collection.ImmutableList;

@KeYGuiExtension.Info(name = "Proof Caching", optional = true,
    description = "TODO",
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
        Proof p = e.getSource();
        if (e.getRuleAppInfo().getOriginalNode().getNodeInfo().getInteractiveRuleApplication()) {
            return; // only applies for automatic proof search
        }
        ImmutableList<Goal> newGoals = e.getNewGoals();
        if (newGoals.size() <= 1) {
            return;
        }
        for (Goal goal : newGoals) {
            ClosedBy c = ReferenceSearcher.findPreviousProof(mediator, goal.node());
            if (c != null) {
                p.closeGoal(goal);
                goal.node().register(c, ClosedBy.class);
            }
        }
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        this.mediator = mediator;
        mediator.addKeYSelectionListener(this);
    }
}
