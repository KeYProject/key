package de.uka.ilkd.key.nui.controller;

import java.io.File;
import java.net.URL;
import java.util.AbstractMap.SimpleImmutableEntry;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.ResourceBundle;
import java.util.stream.Collectors;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nui.ComponentFactory;
import de.uka.ilkd.key.nui.NUI;
import de.uka.ilkd.key.nui.controller.NUIController.Place;
import de.uka.ilkd.key.nui.prooftree.NUINode;
import de.uka.ilkd.key.nui.prooftree.ProofTreeActions;
import de.uka.ilkd.key.nui.prooftree.ProofTreeCell;
import de.uka.ilkd.key.nui.prooftree.ProofTreeVisualizer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import javafx.application.Platform;
import javafx.event.EventHandler;
import javafx.fxml.FXML;
import javafx.fxml.Initializable;
import javafx.scene.control.TreeCell;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyEvent;
import javafx.util.Callback;

/**
 * Controller for the treeView GUI element to visualize proofs.
 * 
 * @author Patrick Jattke
 * @author Matthias Schultheis
 * @author Stefan Pilot
 * @version 1.1
 */
public class TreeViewController implements Initializable {
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
     * Initialization method for scene; loads the default proof.
     */
    @Override
    public final void initialize(final URL location, final ResourceBundle resources) {

        // Register KeyEvent
        Platform.runLater(new Runnable() {
            @Override
            public void run() {
                NUIController.getInstance().registerKeyListener(KeyCode.F,
                        new KeyCode[] { KeyCode.CONTROL }, new EventHandler<KeyEvent>() {
                    @Override
                    public void handle(final KeyEvent e) {
                        if (NUIController.getInstance().getPlaceComponent()
                                .containsKey("treeView")) {
                            Place p = NUIController.getInstance().getPlaceComponent()
                                    .get("treeView");
                            try {
                                NUIController.getInstance().createOrMoveOrHideComponent(
                                        ".searchView", p, ".searchView.fxml");
                            }
                            catch (IllegalArgumentException ex) {
                                // SearchView already exists
                                SearchViewController c = ComponentFactory.getInstance().getController("searchView");
                                c.performFocusRequest();
                            }
                        }
                    }
                });

                NUIController.getInstance().registerKeyListener(KeyCode.ESCAPE, null,
                        new EventHandler<KeyEvent>() {
                    @Override
                    public void handle(final KeyEvent e) {
                        NUIController.getInstance().createOrMoveOrHideComponent(".searchView",
                                Place.HIDDEN, ".searchView.fxml");
                    }
                });

            }
        });

        // set cell factory for rendering cells
        proofTreeView.setCellFactory(new Callback<TreeView<NUINode>, TreeCell<NUINode>>() {
            @Override
            public TreeCell<NUINode> call(final TreeView<NUINode> p) {
                return new ProofTreeCell();
            }
        });

        // Create a new tree visualizer instance for processing the conversion
        // de.uka.ilkd.key.proof.Node -->
        // de.uka.ilkd.key.nui.NUI.prooftree.NUINode
        // --> TreeItem<NUINode> (JavaFX)
        visualizer = new ProofTreeVisualizer(proofTreeView);

        // add CSS file to view
        String cssPath = this.getClass().getResource("../components/treeView.css").toExternalForm();
        visualizer.addStylesheet(cssPath);

        if (NUI.initialProofFile != null) {
            loadAndDisplayProof(NUI.initialProofFile);
        }
    }

    /**
     * Displays a proof in the proofTreeView.
     * 
     * @param proof
     *            The proof file which should be displayed
     */
    private void displayProof(final Proof proof) {
        visualizer.loadProofTree(proof);
        visualizer.visualizeProofTree();
    }

    /**
     * 
     * @param file
     */
    public final void loadAndDisplayProof(File file) {
        displayProof(loadProof(file));
        searchMap = null;
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
        File proofFile = new File("resources//de/uka//ilkd//key//examples//gcd.twoJoins.proof");
        loadAndDisplayProof(proofFile);
        searchMap = null;
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
            Proof proof = environment.getLoadedProof();
            return proof;
        }
        catch (ProblemLoaderException e) {
            e.printStackTrace();
            return null;
        }
    }

    /**
     * Stores all the Labels in the tree and their respective TreeItems.
     */
    private HashMap<String, TreeItem<NUINode>> searchMap;

    public final int getCurrentlySelectedItemsIndex() {
        return proofTreeView.getSelectionModel().getSelectedIndex();
    }

    public final int getTreeItemsRow(TreeItem<NUINode> t) {
        return proofTreeView.getRow(t);
    }

    /**
     * 
     * @return
     */
    public final Map<String, TreeItem<NUINode>> getSearchMap() {

        class TreeToListHelper {
            /**
             * Parses a Tree, beginning at <b>t</b>, and adds to list every
             * TreeItem that is a child of <b>root</b> or of its children
             * <b>l</b>.
             * 
             * @param root
             *            Where to start parsing
             * @param list
             *            Where all the TreeItems are added to
             * @return <b>list</b>, but with all the TreeItems appended to it
             */
            private List<TreeItem<NUINode>> treeToList(final TreeItem<NUINode> root,
                    final List<TreeItem<NUINode>> list) {
                if (root == null || list == null) {
                    throw new IllegalArgumentException();
                }
                list.add(root);
                if (!root.getChildren().isEmpty()) {
                    for (TreeItem<NUINode> ti : root.getChildren()) {
                        list.addAll(treeToList(ti, new LinkedList<TreeItem<NUINode>>()));
                    }
                }
                return list;
            }
        }

        if (searchMap == null) {
            searchMap = new HashMap<>();
            List<TreeItem<NUINode>> l = (new TreeToListHelper()).treeToList(proofTreeView.getRoot(),
                    new LinkedList<TreeItem<NUINode>>());
            for (TreeItem<NUINode> t : l) {
                searchMap.put(t.getValue().getLabel(), t);
            }
        }
        return searchMap;
    }

    public void scrollToAndSelect(int nextLargerIdx) {
        proofTreeView.scrollTo(nextLargerIdx);
        proofTreeView.getSelectionModel().select(nextLargerIdx);
    }
}
