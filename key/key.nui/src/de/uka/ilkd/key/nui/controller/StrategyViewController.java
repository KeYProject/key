package de.uka.ilkd.key.nui.controller;

import de.uka.ilkd.key.nui.TreeViewState;
import de.uka.ilkd.key.nui.exceptions.ControllerNotFoundException;
import de.uka.ilkd.key.nui.prooftree.ProofTreeConverter;
import de.uka.ilkd.key.nui.prooftree.ProofTreeItem;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.ProofStarter;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.Slider;
import javafx.util.StringConverter;

/**
 * 
 * @author Florian Breitfelder
 *
 */
@ControllerAnnotation(createMenu = true)
public class StrategyViewController extends NUIController {

    @FXML
    private Button goButton;

    @FXML
    private Slider maxRuleAppSlider;

    @FXML
    private Label maxRuleAppLabel;

    @Override
    protected void init() {
        // TODO Auto-generated method stub
        maxRuleAppSlider.setLabelFormatter(new StringConverter<Double>() {
            @Override
            public String toString(Double n) {
                int val = (int) Math.pow(10, n);
                return "" + (val >= 10000 ? val >= 1000000
                        ? (val / 1000000) + "M" : (val / 1000) + "k" : +val);
            }

            @Override
            public Double fromString(String string) {
                // TODO Auto-generated method stub
                return null;
            }
        });

        maxRuleAppSlider.valueProperty()
                .addListener(new ChangeListener<Number>() {
                    public void changed(ObservableValue<? extends Number> ov,
                            Number old_val, Number new_val) {
                        maxRuleAppLabel.setText(bundle
                                .getString("maxRuleAppLabel") + " "
                                + (int) Math.pow(10, new_val.doubleValue()));
                    }
                });
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
