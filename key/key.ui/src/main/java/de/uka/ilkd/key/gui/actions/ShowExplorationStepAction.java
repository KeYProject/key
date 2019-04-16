package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.proofExploration.ExplorationStepsList;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;

import java.awt.event.ActionEvent;

public class ShowExplorationStepAction extends MainWindowAction {

    public ShowExplorationStepAction(MainWindow mainWindow) {
        super(mainWindow);
        this.setName("Show Exploration Steps");
    }

    @Override
    public void actionPerformed(ActionEvent e) {

        ExplorationStepsList el = new ExplorationStepsList("Test", this.getMediator().getSelectedProof());
        this.getMediator().getSelectedProof().addProofTreeListener(new ProofTreeListener() {
            @Override
            public void proofExpanded(ProofTreeEvent e) {

            }

            @Override
            public void proofIsBeingPruned(ProofTreeEvent e) {

            }

            @Override
            public void proofPruned(ProofTreeEvent e) {

            }

            @Override
            public void proofStructureChanged(ProofTreeEvent e) {

            }

            @Override
            public void proofClosed(ProofTreeEvent e) {

            }

            @Override
            public void proofGoalRemoved(ProofTreeEvent e) {

            }

            @Override
            public void proofGoalsAdded(ProofTreeEvent e) {

            }

            @Override
            public void proofGoalsChanged(ProofTreeEvent e) {

            }

            @Override
            public void smtDataUpdate(ProofTreeEvent e) {

            }

            @Override
            public void notesChanged(ProofTreeEvent e) {

            }
        });
        el.setVisible(true);
    }
}
