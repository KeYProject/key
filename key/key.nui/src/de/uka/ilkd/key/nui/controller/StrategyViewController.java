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
@SuppressWarnings({ "PMD.TooManyFields", "PMD.AtLeastOneConstructor",
        "PMD.AvoidDuplicateLiterals" })
public class StrategyViewController extends NUIController implements Observer {
    /**
     * The constant 10.
     */
    private static final int TEN = 10;
    /**
     * [1, 6].
     */
    private static final int[] RNG_ONE_TO_SIX = { 1, 2, 3, 4, 5, 6 };
    /**
     * The constant 9.
     */
    private static final int NINE = 9;
    /**
     * The constant 1000.
     */
    private static final int ONETHOUSAND = 1000;
    /**
     * The constant 10000.
     */
    private static final int TENTHOUSAND = 10000;
    /**
     * The constant 100000.
     */
    private static final int ONE_HUNDRED_THOUSAND = 100000; // NOPMD name is fine
    /**
     * The constant 1000000.
     */
    private static final int ONE_MILLION = 1000000; // NOPMD name is fine

    /**
     * The default value for the maximum number of rule applications.
     */
    private static int defaultMaxRuleApplications = TEN; //NOPMD name is fine... sort of

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.LongVariable" })
    private ToggleGroup arithmeticTreatment;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.LongVariable", "PMD.CommentRequired" })
    private ToggleGroup autoInduction;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private ToggleGroup blockTreatment;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private ToggleGroup classAxiom;

    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private transient int currSliderVal = defaultMaxRuleApplications;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired", "PMD.LongVariable" })
    private ToggleGroup dependencyContracts;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired", "PMD.LongVariable" })
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
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired", "PMD.LongVariable" })
    private transient AnchorPane proofSearchStrategy;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired" })
    private ToggleGroup proofSplitting;

    @FXML
    @SuppressWarnings({ "PMD.UnusedPrivateField", "PMD.CommentRequired", "PMD.LongVariable" })
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
     * Getter.
     * 
     * @return an {@link ImageView} containing the "Go"-Button image
     */
    public ImageView getGoButtonImage() {
        return goButtonImage;
    }

    /**
     * Getter.
     * 
     * @return the {@link StrategyWrapper}.
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
        if (getDataModel().getLoadedTreeViewState() == null) {
            getNui().updateStatusbar(getBundle().getString("errorProofFileMissing"));

        }
        else {

            final String filename = getDataModel().getLoadedTreeViewState().getProof()
                    .getProofFile().getName();

            // retrieve proof file and init proofStarter

            final TreeViewState treeViewState = getDataModel().getTreeViewState(filename);
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
            getNui().updateStatusbar(strategyInfo.reason());

            // if automatic rule application could not be performed -> no
            // rendering
            // of proof required
            if (strategyInfo.getAppliedRuleApps() > 0) {
                // load updated proof
                final Proof updatedProof = proofStarter.getProof();

                // create new tree from updateProof

                final ProofTreeItem fxtree = new ProofTreeConverter(updatedProof)
                        .createFXProofTree();

                // Create new TreeViewState for updatedProof and update
                // getDataModel()
                getDataModel().saveTreeViewState(new TreeViewState(updatedProof, fxtree), filename);

            }
        }
    }

    /**
     * Setter.
     * 
     * @param goButtonImage
     *            an {@link ImageView}.
     */
    public void setGoButtonImage(final ImageView goButtonImage) {
        this.goButtonImage = goButtonImage;
    }

    /**
     * Setter.
     * 
     * @param strategyWrapper
     *            a {@link StrategyWrapper}.
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
        final double vWNOAN = sliderValue % NINE;

        if (sliderValue > 0 && sliderValue < 1) {
            currSliderVal = (int) Math.floor(vWNOAN * TEN) + 1;
        }
        else {
            final double sliderCoefficient = Math.pow(TEN, roundSliderValue);
            if (Arrays.asList(RNG_ONE_TO_SIX).contains(sliderValue)) {
                currSliderVal = (int) sliderCoefficient;
            }
            else {
                currSliderVal = (int) (Math.floor((vWNOAN - roundSliderValue) * TEN)
                        * sliderCoefficient + sliderCoefficient);
            }
        }
    }

    @Override
    protected void init() {
        getDataModel().addObserver(this);
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
                final int val = (int) Math.pow(TEN, number);

                if (val < TEN) {
                    return String.valueOf(val);
                }
                if (val < TENTHOUSAND) {
                    return String.valueOf(val);
                }
                if (val < ONE_MILLION) {
                    return (val / ONETHOUSAND) + "k";
                }
                return (val / ONE_HUNDRED_THOUSAND) + "M";
            }
        });

        // Adds a listener to the 'Maximum rules' slider, used to update the
        // label with the currently chosen value

        maxRuleAppSlider.valueProperty().addListener((obs, oldVal, newVal) -> {
            calculateCurrentSliderValue(newVal);
            maxRuleAppLabel.setText(getBundle().getString("maxRuleAppLabel") + " " + currSliderVal);

        });
        maxRuleAppLabel.setText(getBundle().getString("maxRuleAppLabel") + " " + currSliderVal);
    }

}
