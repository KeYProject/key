package de.uka.ilkd.key.nui.controller;

import java.util.Observable;
import java.util.Observer;

import de.uka.ilkd.key.nui.DataModel;
import de.uka.ilkd.key.nui.TreeViewState;
import javafx.fxml.FXML;
import javafx.scene.control.TextArea;

/**
 * Controller for the view showing the proof file statistics.
 * 
 * @author Florian Breitfelder
 *
 */
@ControllerAnnotation(createMenu = true)
public class ProofViewController extends NUIController implements Observer {

    @FXML
    private TextArea textAreaProof;

    @Override
    protected void init() {
        dataModel.addObserver(this);
    }

    @Override
    public void update(final Observable observable, final Object arg) {
        final TreeViewState treeViewState = dataModel
                .getTreeViewState(arg.toString());
        if (treeViewState != null) {
            textAreaProof.setText(
                    treeViewState.getProof().getStatistics().toString());
        }
        else if (((DataModel) observable).getListOfProofs().size() >= 1) {
            textAreaProof.setText(bundle.getString("noProofSelected"));
        }
        else {
            textAreaProof.setText(bundle.getString("noProofLoaded"));
        }
    }
}
