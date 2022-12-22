package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import java.util.Collection;
import java.util.stream.Collectors;

/**
 * User action that modifies the proof in some way.
 * On undo: prunes proof to previous collection of open goals, selects previously active node.
 */
public abstract class ProofModifyingUserAction extends UserAction {
    private Collection<Node> originalOpenGoals;
    private Node originalSelection;

    protected ProofModifyingUserAction(KeYMediator mediator, Proof originalState) {
        super(mediator);
        this.originalOpenGoals =
            originalState.openGoals().stream().map(Goal::node).collect(Collectors.toList());
        this.originalSelection = mediator.getSelectedNode();
    }

    @Override
    public void undo() {
        for (Node n : originalOpenGoals) {
            n.proof().pruneProof(n);
        }
        mediator.getSelectionModel().setSelectedNode(originalSelection);
    }
}
