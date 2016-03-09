package de.uka.ilkd.key.nui.controller;

import de.uka.ilkd.key.nui.TreeViewState;
import de.uka.ilkd.key.nui.exceptions.ControllerNotFoundException;
import de.uka.ilkd.key.nui.prooftree.ProofTreeConverter;
import de.uka.ilkd.key.nui.prooftree.ProofTreeItem;
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
            nui.updateStatusbar("A proof file must be loaded first!");
            return;
        }

        // retrieve proof file and init proofStarter
        TreeViewState treeViewState = dataModel.getTreeViewState(filename);
        Proof p = treeViewState.getProof();
        proofStarter.init(p);

        // start automatic proof
        ApplyStrategyInfo strategyInfo = proofStarter.start();

        // update statusbar
        nui.updateStatusbar(strategyInfo.reason());

        // load updated proof
        Proof updatedProof = proofStarter.getProof();

        // create new tree from updateProof
        ProofTreeItem fxtree = new ProofTreeConverter(updatedProof)
                .createFXProofTree();

        // Create new TreeViewState for updatedProof
        TreeViewState updatedTreeViewState = new TreeViewState(updatedProof,
                fxtree);

        // update datamodel
        dataModel.updateTreeViewState(filename, updatedTreeViewState);
    }

}
