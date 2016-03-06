package de.uka.ilkd.key.nui.controller;

import java.util.Observable;
import java.util.Observer;

import de.uka.ilkd.key.nui.TreeViewState;
import javafx.fxml.FXML;
import javafx.scene.control.TextArea;

public class OpenProofsViewController extends NUIController
        implements Observer {

    @FXML
    TextArea textAreaOpenProofs;

    @Override
    protected void init() {
        dataModel.addObserver(this);
    }

    @Override
    public void update(Observable o, Object arg) {
        TreeViewState treeViewState = dataModel
                .getTreeViewState(arg.toString());
        textAreaOpenProofs.setText(treeViewState.getProof().getProofFile().getName());
    }

}
