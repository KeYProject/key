package de.uka.ilkd.key.nui.controller;

import de.uka.ilkd.key.nui.TreeViewState;
import de.uka.ilkd.key.nui.exceptions.ControllerNotFoundException;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.ProofStarter;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.scene.control.Button;

public class StrategyViewController extends NUIController {

    @FXML
    private Button goButton;

    @Override
    protected void init() {
        // TODO Auto-generated method stub

    }

    public void handleOnAction(final ActionEvent e)
            throws ControllerNotFoundException {

        ProofStarter proofStarter = new ProofStarter(false);
        String filename;

        try {

            filename = dataModel.getLoadedTreeViewState().getProof()
                    .getProofFile().getName();

        }
        catch (NullPointerException e2) {
            ((MainViewController) nui.getController("MainView"))
                    .updateStatusbar("A proof file must be loaded first!");
            return;
        }

        // retrieve proof file and init proofStarter
        TreeViewState treeViewState = dataModel.getTreeViewState(filename);
        Proof p = treeViewState.getProof();
        proofStarter.init(p);

        // start automatic proof
        ApplyStrategyInfo strategyInfo = proofStarter.start();

        // update statusbar
        ((MainViewController) nui.getController("MainView"))
                .updateStatusbar(strategyInfo.reason());

        // save changed proof into data model
        TreeViewState newTreeViewState = new TreeViewState(
                proofStarter.getProof(), treeViewState.getTreeItem());
        dataModel.saveTreeViewState(newTreeViewState, filename);

    }

}
