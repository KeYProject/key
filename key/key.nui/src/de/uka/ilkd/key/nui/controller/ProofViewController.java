package de.uka.ilkd.key.nui.controller;

import java.util.Observable;
import java.util.Observer;

import de.uka.ilkd.key.nui.TreeViewState;
import javafx.fxml.FXML;
import javafx.scene.control.ListView;
import javafx.scene.control.TextArea;

public class ProofViewController extends NUIController implements Observer {

    @FXML
    TextArea textAreaProof;

    @Override
    protected void init() {
        dataModel.addObserver(this);
    }

    @Override
    public void update(Observable o, Object arg) {
        TreeViewState treeViewState = dataModel
                .getTreeViewState(arg.toString());
        textAreaProof.setText(treeViewState.getProof().toString());
    }

}
