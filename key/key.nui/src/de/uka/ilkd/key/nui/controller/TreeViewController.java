package de.uka.ilkd.key.nui.controller;

import java.io.File;

import java.net.URL;
import java.util.Collections;

import java.util.ResourceBundle;
import java.util.Set;
import java.util.WeakHashMap;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nui.IconFactory;
import de.uka.ilkd.key.nui.NUI;
import de.uka.ilkd.key.nui.prooftree.NUINode;
import de.uka.ilkd.key.nui.prooftree.ProofTreeCell;
import de.uka.ilkd.key.nui.prooftree.ProofTreeStyle;
import de.uka.ilkd.key.nui.prooftree.ProofTreeVisualizer;
import de.uka.ilkd.key.nui.prooftree.SearchHelper;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import javafx.application.Platform;

import javafx.fxml.FXML;
import javafx.fxml.Initializable;
import javafx.scene.control.TreeView;
import javafx.scene.input.KeyCode;
import javafx.scene.layout.VBox;

/**
 * Controller for the treeView GUI element to visualize proofs.
 * 
 * @author Patrick Jattke
 * @author Matthias Schultheis
 * @author Stefan Pilot
 * @version 1.1
 */
public class TreeViewController implements Initializable {

    public static final String NAME = "treeView";
    public static final String RESOURCE = "treeView.fxml";

    /**
     * The IconFactory used to create icons for the proof tree nodes.
     */
    private final IconFactory icf;

    /**
     * The VBox containing both the TreeView and the Anchor Pane where the
     * Search elements are
     */
    @FXML
    private VBox mainVBox;

    private final Set<ProofTreeCell> proofTreeCells = Collections
            .newSetFromMap(new WeakHashMap<>());

    /**
     * The proofTree view of the GUI.
     */
    @FXML
    private TreeView<NUINode> proofTreeView;

    private SearchHelper searchHelper = null;

    /**
     * The visualizer for displaying a proof tree.
     */
    private ProofTreeVisualizer visualizer;

    /**
     * The constructor.
     */
    public TreeViewController() {
        icf = new IconFactory(ProofTreeCell.ICON_SIZE, ProofTreeCell.ICON_SIZE);
    }

    /**
     * Initialization method for scene; loads the default proof.
     */
    @Override
    public final void initialize(final URL location, final ResourceBundle resources) {
        Platform.runLater(() -> {

            // Register KeyEvent
            NUIController.getInstance().registerKeyListener(KeyCode.F,
                    new KeyCode[] { KeyCode.CONTROL }, (event) -> {
                if (searchHelper != null) {
                    searchHelper.performFocusRequest();
                }
                else {
                    searchHelper = new SearchHelper(proofTreeView, proofTreeCells, mainVBox);
                }
            });

            NUIController.getInstance().registerKeyListener(KeyCode.ESCAPE, null, (event) -> {
                searchHelper.destructor();
                searchHelper = null;
            });
        });

        proofTreeView.getStyleClass().add(ProofTreeStyle.CSS_PROOF_TREE);

        // set cell factory for rendering cells
        proofTreeView.setCellFactory((treeItem) -> {
            ProofTreeCell c = new ProofTreeCell(icf);
            Platform.runLater(() -> registerTreeCell(c));
            return c;
        });

        // Create a new tree visualizer instance for processing the conversion
        // de.uka.ilkd.key.proof.Node -->
        // de.uka.ilkd.key.nui.NUI.prooftree.NUINode
        // --> TreeItem<NUINode> (JavaFX)
        visualizer = new ProofTreeVisualizer(proofTreeView);

        // add CSS file to view
        final String cssPath = this.getClass()
                .getResource("../components/" + ProofTreeStyle.CSS_FILE).toExternalForm();
        visualizer.addStylesheet(cssPath);

        if (NUI.getInitialProofFile() != null) {
            loadAndDisplayProof(NUI.getInitialProofFile());
        }
    }

    /**
     * Loads and displays a file containing a KeY proof. May fail and/or throw
     * various exceptions if the file does not exist or does not contain a valid
     * proof.
     * 
     * @param file
     *            The proof file to load.
     */
    public final void loadAndDisplayProof(final File file) {
        visualizer.loadProofTree(loadProof(file));
        visualizer.visualizeProofTree();
        if (searchHelper != null) {
            searchHelper.destructor();
            searchHelper = null;
        }
    }

    /**
     * Loads the given proof file. Checks if the proof file exists and the proof
     * is not null, and fails if the proof could not be loaded.
     *
     * @param proofFileName
     *            The file name of the proof file to load.
     * @return The loaded proof.
     */
    public final void loadExampleProof() {
        if (searchHelper != null) {
            searchHelper.destructor();
            searchHelper = null;
        }
        File proofFile = new File("resources//de/uka//ilkd//key//examples//gcd.twoJoins.proof");
        loadAndDisplayProof(proofFile);
    }

    /**
     * Loads the given proof file. Checks if the proof file exists and the proof
     * is not null, and fails if the proof could not be loaded.
     *
     * @param proofFileName
     *            The file name of the proof file to load.
     * @return The loaded proof.
     */
    private Proof loadProof(final File proofFile) {
        try {
            KeYEnvironment<?> environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(),
                    proofFile, null, null, null, true);
            final Proof proof = environment.getLoadedProof();
            return proof;
        }
        catch (ProblemLoaderException e) {
            e.printStackTrace();
            return null;
        }
    }

    /**
     * This method should be called every time a new TreeCell is being created.
     * <tt>this</tt> will reference the ProofTreeCell in a WeakHandle in order
     * to find out which TreeItems currently are visible to the user. This is
     * needed because TreeView does not provide something like getTreeCells
     *
     * @param treeCell
     *            the ProofTreeCell to register.
     */
    private void registerTreeCell(final ProofTreeCell treeCell) {
        proofTreeCells.add(treeCell);
    }
}
