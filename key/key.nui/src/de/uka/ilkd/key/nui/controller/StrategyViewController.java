package de.uka.ilkd.key.nui.controller;

import java.util.Arrays;
import java.util.Observable;
import java.util.Observer;

import javax.swing.SwingUtilities;

import de.uka.ilkd.key.nui.DataModel;
import de.uka.ilkd.key.nui.IconFactory;
import de.uka.ilkd.key.nui.TreeViewState;
import de.uka.ilkd.key.nui.exceptions.ControllerNotFoundException;
import de.uka.ilkd.key.nui.prooftree.ProofTreeConverter;
import de.uka.ilkd.key.nui.prooftree.ProofTreeItem;
import de.uka.ilkd.key.nui.wrapper.StrategyWrapper;

import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Proof;

import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.util.ProofStarter;

import javafx.application.Platform;
import javafx.embed.swing.SwingNode;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.Slider;
import javafx.scene.control.ToggleGroup;
import javafx.scene.image.ImageView;
import javafx.scene.layout.AnchorPane;
import javafx.util.StringConverter;

/**
 * Controller for StrategyView GUI element, used to show proof strategy options.
 * 
 * @author Florian Breitfelder
 *
 */
@ControllerAnnotation(createMenu = true)
public class StrategyViewController extends NUIController implements Observer {

    /**
     * The default value for the maximum number of rule applications.
     */
    private static int defaultMaxRuleApplications = 10;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired",
            "PMD.AvoidDuplicateLiterals" })
    private ToggleGroup arithmeticTreatment;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private ToggleGroup autoInduction;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private ToggleGroup blockTreatment;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private ToggleGroup classAxiom;

    /**
     * The current value of the slider.
     */
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private int currSliderVal = defaultMaxRuleApplications;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private ToggleGroup dependencyContracts;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private ToggleGroup expandLocalQueries;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired",
            "PMD.AvoidDuplicateLiterals" })
    private Button goButton;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private ImageView goButtonImage;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private ToggleGroup loopTreatment;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private transient Label maxRuleAppLabel;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private transient Slider maxRuleAppSlider;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private ToggleGroup methodTreatment;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private transient AnchorPane proofSearchStrategy;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private ToggleGroup proofSplitting;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private ToggleGroup quantifierTreatment;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private ToggleGroup queryTreatment;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private ToggleGroup stopAt;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private AnchorPane strategyViewPane;

    /**
     * The instance of the strategyWrapper containing the radio buttons of the
     * StrategyView.
     */

    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })

    private StrategyWrapper strategyWrapper;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private ToggleGroup userOptions1;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private ToggleGroup userOptions2;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private ToggleGroup userOptions3;

    /**
     * TODO
     * 
     * @return
     */
    public int getCurrentSliderValue() {
        return currSliderVal;
    }

    /**
     * TODO
     * 
     * @return
     */
    public ImageView getGoButtonImage() {
        return goButtonImage;
    }

    /**
     * TODO
     * 
     * @return
     */
    public StrategyWrapper getStrategyWrapper() {
        return strategyWrapper;
    }

    /**
     * Action handler for the 'Start' (auto proving) button.
     * 
     * @param actionEvent
     * @throws ControllerNotFoundException
     */
    public void handleOnAction(final ActionEvent actionEvent) throws ControllerNotFoundException {

        final String filename;
        final TreeViewState loadedTreeViewState = dataModel.getLoadedTreeViewState();
        if (loadedTreeViewState == null) {
            nui.updateStatusbar(bundle.getString("errorProofFileMissing"));

        }
        else {

            filename = dataModel.getLoadedTreeViewState().getProof().getProofFile().getName();

            // retrieve proof file and init proofStarter

            final TreeViewState treeViewState = dataModel.getTreeViewState(filename);
            final Proof proof = treeViewState.getProof();
            final ProofStarter proofStarter = new ProofStarter(false);
            proofStarter.init(proof);

            // TODO
            final Strategy strategy = strategyWrapper.getStrategy();
            proofStarter.setStrategy(strategy);
            // restrict maximum number of rule applications based on slider
            // value
            // only set value of slider if slider was moved
            if (currSliderVal > 0) {
                proofStarter.setMaxRuleApplications(currSliderVal);
            }

            // start automatic proof
            final ApplyStrategyInfo strategyInfo = proofStarter.start();

            // update statusbar
            nui.updateStatusbar(strategyInfo.reason());

            // if automatic rule application could not be performed -> no
            // rendering
            // of proof required
            if (strategyInfo.getAppliedRuleApps() > 0) {
                // load updated proof
                final Proof updatedProof = proofStarter.getProof();

                // create new tree from updateProof

                final ProofTreeItem fxtree = new ProofTreeConverter(updatedProof)
                        .createFXProofTree();

                // Create new TreeViewState for updatedProof
                final TreeViewState updatedTreeViewState = new TreeViewState(updatedProof, fxtree);

                // update datamodel
                dataModel.saveTreeViewState(updatedTreeViewState, filename);

            }
        }
    }

    /**
     * TODO
     * 
     * @param currSliderVal
     */
    public void setCurrSliderVal(final int currSliderVal) {
        this.currSliderVal = currSliderVal;
    }

    /**
     * TODO
     * 
     * @param goButtonImage
     */
    public void setGoButtonImage(final ImageView goButtonImage) {
        this.goButtonImage = goButtonImage;
    }

    /**
     * TODO
     * 
     * @param strategyWrapper
     */
    public void setStrategyWrapper(final StrategyWrapper strategyWrapper) {
        this.strategyWrapper = strategyWrapper;
    }

    @Override

    public void update(final Observable obs, final Object arg) {
        if (obs instanceof DataModel) {
            final TreeViewState treeViewState = ((DataModel) obs).getTreeViewState(arg.toString());

            if (treeViewState != null) {
                addStrategyViewSwing(treeViewState.getProof());
            }
        }
    }

    /**
     * Adds the StrategySelectionView from Swing to the JavaFX StrategyView.
     * 
     * @param proof
     *            The proof file loaded in the treeView.
     */
    private void addStrategyViewSwing(final Proof proof) {
        proofSearchStrategy.getChildren().clear();
        SwingUtilities.invokeLater(() -> {
            final SwingNode swingNode = strategyWrapper.createStrategyComponent(proof);

            Platform.runLater(() -> proofSearchStrategy.getChildren().add(swingNode));

        });
    }

    /**
     * Calculates the value of the slider based on the current position.
     * 
     * @param newVal
     *            {@link Number} the value obtained from the slider.
     */
    private void calculateCurrentSliderValue(final Number newVal) {
        final double sliderValue = newVal.doubleValue();
        final double roundSliderValue = Math.floor(sliderValue);

        if (sliderValue > 0.0 && sliderValue < 1.0) {
            currSliderVal = (int) Math.floor(sliderValue % 9.0 * 10.0) + 1;
        }
        else {
            final double sliderCoefficient = Math.pow(10, roundSliderValue);
            if (Arrays.asList(new int[] { 1, 2, 3, 4, 5, 6 }).contains(sliderValue)) {
                currSliderVal = (int) sliderCoefficient;
            }
            else {
                currSliderVal = (int) (Math.floor((sliderValue % 9.0 - roundSliderValue) * 10)
                        * sliderCoefficient + sliderCoefficient);
            }
        }
    }

    @Override
    protected void init() {
        dataModel.addObserver(this);
        strategyWrapper = new StrategyWrapper();
        addStrategyViewSwing(null);
        final IconFactory iconFactory = new IconFactory(15, 15);

        goButtonImage.setImage(iconFactory.getImage(IconFactory.GO_BUTTON).getImage());

        // Set formatter of 'Maximum rules' slider

        maxRuleAppSlider.setLabelFormatter(new StringConverter<Double>() {
            @Override
            public Double fromString(final String string) {
                return null;
            }

            @Override
            public String toString(final Double number) {
                final int val = (int) Math.pow(10, number);
                if (val < 10000) {
                    return String.valueOf(val);
                }
                if (val < 1000000) {
                    return (val / 1000) + "k";
                }
                return (val / 1000000) + "M";

            }
        });

        // Adds a listener to the 'Maximum rules' slider, used to update the
        // label with the currently chosen value

        maxRuleAppSlider.valueProperty().addListener((obs, oldVal, newVal) -> {
            calculateCurrentSliderValue(newVal);
            maxRuleAppLabel.setText(bundle.getString("maxRuleAppLabel") + " " + currSliderVal);

        });
        maxRuleAppLabel.setText(bundle.getString("maxRuleAppLabel") + " " + currSliderVal);
    }

}
