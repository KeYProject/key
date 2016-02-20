package de.uka.ilkd.key.nui.controller;

import java.io.File;
import java.util.Collections;
import java.util.Observable;
import java.util.Observer;
import java.util.Set;
import java.util.WeakHashMap;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nui.DataModel;
import de.uka.ilkd.key.nui.IconFactory;
import de.uka.ilkd.key.nui.NUI;
import de.uka.ilkd.key.nui.TreeViewState;
import de.uka.ilkd.key.nui.exceptions.ComponentNotFoundException;
import de.uka.ilkd.key.nui.exceptions.ControllerNotFoundException;
import de.uka.ilkd.key.nui.prooftree.NUINode;
import de.uka.ilkd.key.nui.prooftree.ProofTreeCell;
import de.uka.ilkd.key.nui.prooftree.ProofTreeStyle;
import de.uka.ilkd.key.nui.prooftree.ProofTreeVisualizer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import javafx.application.Platform;
import javafx.fxml.FXML;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;
import javafx.scene.input.KeyCode;
import javafx.scene.layout.Pane;
import javafx.scene.layout.VBox;

/**
 * Controller for the treeView GUI element to visualize proofs.
 * 
 * @author Patrick Jattke
 * @author Matthias Schultheis
 * @author Stefan Pilot
 * @author Florian Breitfelder
 * @version 1.1
 */
public class TreeViewController extends NUIController implements Observer {

    /**
     * The name of the GUI component.
     */
    public static final String NAME = "treeView";

    /**
     * The fxml file name.
     */
    public static final String RESOURCE = "treeView.fxml";

    /**
     * The IconFactory used to create icons for the proof tree nodes.
     */
    private IconFactory icf;

    /**
     * The VBox containing both the TreeView and the Anchor Pane where the
     * Search elements are.
     */
    @FXML
    private VBox treeViewPane;

    /**
     * The tree cells used for displaying tree nodes.
     */
    private final Set<ProofTreeCell> proofTreeCells = Collections
            .newSetFromMap(new WeakHashMap<>());

    /**
     * Stores the last loaded proof. 
     */
    private Proof loadedProof = null;
    
    /**
     * The proofTree view of the GUI.
     */
    @FXML
    private TreeView<NUINode> proofTreeView;

    /**
     * The visualizer for displaying a proof tree.
     */
    private ProofTreeVisualizer visualizer;

    /**
     * Loads and displays a file containing a KeY proof. May fail and/or throw
     * various exceptions if the file does not exist or does not contain a valid
     * proof.
     * 
     * @param file
     *            The proof file to load.
     */
    public final void loadAndDisplayProof(final File file) {
        loadedProof = loadProof(file);
        loadedProof.setProofFile(file);
        
        visualizer.loadProofTree(loadedProof);
        TreeItem<NUINode> tree = visualizer.visualizeProofTree();

        // Store state of treeView into data model
        nui.getDataModel().saveTreeViewState(new TreeViewState(loadedProof, tree),
                file.getName());
    }

    /**
     * Loads the given proof file. Checks if the proof file exists and the proof
     * is not null, and fails if the proof could not be loaded.
     *
     * @param proofFileName
     *            The file name of the proof file to load.
     * @return The loaded proof.
     */
    private Proof loadProof(final File proofFileName) {
        try {
            final KeYEnvironment<?> environment = KeYEnvironment.load(
                    JavaProfile.getDefaultInstance(), proofFileName, null, null,
                    null, true);
            final Proof proof = environment.getLoadedProof();
            return proof;
        }
        catch (ProblemLoaderException e) {
            // TODO exception handling
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

    /**
     * Opens the search View or moves the focus to the search views text field
     * if a search view already exists.
     */
    public final void openSearchView() {

        try {
            ((SearchViewController) nui.getController("searchView"))
                    .initSearch(proofTreeView, proofTreeCells, treeViewPane);
        }
        catch (ControllerNotFoundException exception) {
            exception.showMessage();
        }

        try {
            Pane searchView = nui.getComponent("searchView");
            if (!treeViewPane.getChildren().contains(searchView))
                treeViewPane.getChildren().add(searchView);
        }
        catch (ComponentNotFoundException exception) {
            exception.showMessage();
        }

    }

    /**
     * init() is called by the NUIController constructor
     */
    @Override
    protected void init() {
        icf = new IconFactory(ProofTreeCell.ICON_SIZE, ProofTreeCell.ICON_SIZE);

        Platform.runLater(() -> {

            // Register key listeners
            final KeyCode[] modStrg = { KeyCode.CONTROL };

            // listener for opening search view
            // MainViewController.getInstance().registerKeyListener(KeyCode.F,
            // modStrg, (event) -> openSearchView());
            try {
                ((MainViewController) nui.getController("MainView"))
                        .registerKeyListener(KeyCode.F, modStrg,
                                (event) -> openSearchView());
            }
            catch (ControllerNotFoundException exception) {
                exception.showMessage();
            }

            // listener for closing search and filter view
            /*
             * MainViewController.getInstance().registerKeyListener(KeyCode.
             * ESCAPE, null, (event) -> { if (searchHandler != null) {
             * searchHandler.destruct(); searchHandler = null; }
             * 
             * //TODO filtering });
             */

            proofTreeView.getStyleClass().add(ProofTreeStyle.CSS_PROOF_TREE);

            // set cell factory for rendering cells
            proofTreeView.setCellFactory((treeItem) -> {
                final ProofTreeCell cell = new ProofTreeCell(icf);
                Platform.runLater(() -> registerTreeCell(cell));
                return cell;
            });

            // Create a new tree visualizer instance for processing the
            // conversion
            // de.uka.ilkd.key.proof.Node -->
            // de.uka.ilkd.key.nui.NUI.prooftree.NUINode
            // --> TreeItem<NUINode> (JavaFX)
            visualizer = new ProofTreeVisualizer(proofTreeView);

            // add CSS file to view
            final String cssPath = this.getClass()
                    .getResource("../components/" + ProofTreeStyle.CSS_FILE)
                    .toExternalForm();
            visualizer.addStylesheet(cssPath);

            if (NUI.getInitialProofFile() != null) {
                loadAndDisplayProof(NUI.getInitialProofFile());
            }

        });

        // register to the data model
        nui.getDataModel().addObserver(this);
    }

    @Override
    public void update(Observable o, Object arg) {
        TreeItem<NUINode> treeItem = ((DataModel) o).getTreeViewState((String) arg).getTreeItem();
        // update the proofTreeView component in the treeView
        visualizer.displayProofTree(treeItem);

    }

    /**
     * Returns the last loaded proof.
     */
    public Proof getLoadedProof() {
        return loadedProof;
    }
}
