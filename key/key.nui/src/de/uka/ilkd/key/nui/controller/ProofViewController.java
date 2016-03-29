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
@SuppressWarnings("PMD.AtLeastOneConstructor") // makes no sense in classes marshaled from fxml
public class ProofViewController extends NUIController implements Observer {

    /**
     * The {@link TextArea} where Proof details are displayed.
     */
    @FXML
    private transient TextArea textAreaProof;

    @Override
    public void update(final Observable observable, final Object arg) {
        final TreeViewState treeViewState = getDataModel().getTreeViewState(arg.toString());

        if (treeViewState == null) {
            if (observable instanceof DataModel
                    && ((DataModel) observable).getListOfProofs().size() >= 1) {
                textAreaProof.setText(getBundle().getString("noProofSelected"));
            }
            else {
                textAreaProof.setText(getBundle().getString("noProofLoaded"));
            }
        }
        else {
            textAreaProof.setText(treeViewState.getProof().getStatistics().toString());
        }

    }

    @Override
    protected void init() {
        getDataModel().addObserver(this);
    }
}
