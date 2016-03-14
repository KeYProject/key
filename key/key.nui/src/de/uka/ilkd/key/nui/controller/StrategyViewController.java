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

    private int currentSliderValue = 10;

    @Override
    protected void init() {
        maxRuleAppSlider.setLabelFormatter(new StringConverter<Double>() {
            @Override
            public String toString(Double n) {
                int val = (int) Math.pow(10, n);
                return "" + (val >= 10000 ? val >= 1000000
                        ? (val / 1000000) + "M" : (val / 1000) + "k" : +val);
            }

            @Override
            public Double fromString(String string) {
                return null;
            }
        });

        maxRuleAppSlider.valueProperty()
                .addListener(new ChangeListener<Number>() {
                    public void changed(ObservableValue<? extends Number> ov,
                            Number old_val, Number new_val) {
                        
                        calculateCurrentSliderValue(new_val);
                        maxRuleAppLabel
                                .setText(bundle.getString("maxRuleAppLabel")
                                        + " " + currentSliderValue);
                    }
                });
        maxRuleAppLabel.setText(
                bundle.getString("maxRuleAppLabel") + " " + currentSliderValue);
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
            nui.updateStatusbar(bundle.getString("errorProofFileMissing"));
            return;
        }

        // retrieve proof file and init proofStarter
        TreeViewState treeViewState = dataModel.getTreeViewState(filename);
        Proof p = treeViewState.getProof();
        proofStarter.init(p);

        // restrict maximum number of rule applications based on slider value
        // only set value of slider if slider was moved
        if (currentSliderValue > 0) {
            proofStarter.setMaxRuleApplications(currentSliderValue);
        }
        
        // start automatic proof
        ApplyStrategyInfo strategyInfo = proofStarter.start();

        // update statusbar
        nui.updateStatusbar(strategyInfo.reason());

        // if automatic rule application could not be performed -> no rendering
        // of proof required
        if (strategyInfo.getAppliedRuleApps() > 0) {
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

    private void calculateCurrentSliderValue(Number new_val) {
        if (new_val.doubleValue() > 0.0 && new_val.doubleValue() < 1.0) {
            currentSliderValue = ((int) (new_val.doubleValue() % 9.0 * 10.0))
                    + 1;
        }
        else if (new_val.doubleValue() > 1.0 && new_val.doubleValue() < 2.0) {
            currentSliderValue = ((int) (((new_val.doubleValue() % 9.0) - 1)
                    * 10) * 10) + 10;
        }
        else if (new_val.doubleValue() > 2.0 && new_val.doubleValue() < 3.0) {
            currentSliderValue = ((int) (((new_val.doubleValue() % 9.0) - 2)
                    * 10) * 100) + 100;
        }
        else if (new_val.doubleValue() > 3.0 && new_val.doubleValue() < 4.0) {
            currentSliderValue = ((int) (((new_val.doubleValue() % 9.0) - 3)
                    * 10) * 1000) + 1000;
        }
        else if (new_val.doubleValue() > 4.0 && new_val.doubleValue() < 5.0) {
            currentSliderValue = ((int) (((new_val.doubleValue() % 9.0) - 4)
                    * 10) * 10000) + 10000;
        }
        else if (new_val.doubleValue() > 5.0 && new_val.doubleValue() < 6.0) {
            currentSliderValue = ((int) (((new_val.doubleValue() % 9.0) - 5)
                    * 10) * 100000) + 100000;
        }
        else {
            switch (new_val.intValue()) {
            case 1:
                currentSliderValue = 10;
                break;
            case 2:
                currentSliderValue = 100;
                break;
            case 3:
                currentSliderValue = 1000;
                break;
            case 4:
                currentSliderValue = 10000;
                break;
            case 5:
                currentSliderValue = 100000;
                break;
            case 6:
                currentSliderValue = 1000000;
                break;
            }

        }
    }

}
