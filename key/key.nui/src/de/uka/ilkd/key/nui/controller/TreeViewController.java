package de.uka.ilkd.key.nui.controller;

import java.io.File;
import java.net.URL;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.ResourceBundle;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nui.prooftree.*;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.control.TreeCell;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;
import javafx.util.Callback;

/**
 * controller for the treeView GUI element to visualize proofs
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
     * the visualizer for displaying a proof tree
     */
    ProofTreeVisualizer visualizer;

    /**
     * TODO
     * 
     * @author Stefan Pilot
     */
    private static TreeViewController instance;

    /**
     * Initialization method for scene; loads the default proof
     */
    @Override
    public void initialize(URL location, ResourceBundle resources) {

        instance = this;

        // set cell factory for rendering cells
        proofTreeView.setCellFactory(new Callback<TreeView<NUINode>, TreeCell<NUINode>>() {
            @Override
            public TreeCell<NUINode> call(TreeView<NUINode> p) {
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

        // load and display proof in visualizer
        Proof p = loadProof("gcd.twoJoins.proof");
        displayProof(p);
    }

    /**
     * displays a proof in the proofTreeView
     * 
     * @param proof
     *            The proof file which should be displayed
     */
    private void displayProof(Proof proof) {
        visualizer.loadProofTree(proof);
        visualizer.visualizeProofTree();
    }

    /**
     * Loads the given proof file. Checks if the proof file exists and the proof
     * is not null, and fails if the proof could not be loaded.
     *
     * @param proofFileName
     *            The file name of the proof file to load.
     * @return The loaded proof.
     */
    private Proof loadProof(String proofFileName) {
        String examplesRoot = "resources//de/uka//ilkd//key//examples//";
        File proofFile = new File(examplesRoot + proofFileName);
        try {
            KeYEnvironment<?> environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(), proofFile, null, null,
                    null, true);
            Proof proof = environment.getLoadedProof();
            return proof;
        }
        catch (ProblemLoaderException e) {
            e.printStackTrace();
            return null;
        }
    }

    /**
     * TODO
     * 
     * @author Stefan Pilot
     * @return
     */
    public static TreeViewController getInstance() {
        return instance;
    }

    /**
     * TODO
     * 
     * @author Stefan Pilot
     */
    private TreeItem<NUINode> currentFoundObject;

    /**
     * TODO
     */
    private HashMap<String, TreeItem<NUINode>> searchMap;

    private List<TreeItem<NUINode>> searchResults;

    /**
     * TODO
     * 
     * @author Stefan Pilot
     * @param term
     */
    public void search(String term) {
        if (searchMap == null)
            initializeSearchMap();

        // for(String s : searchMap.keySet()) System.out.println(s);

        if (searchResults != null) {
            for (TreeItem<NUINode> t : searchResults) {
                t.getValue().setHighlighting(false);
            }
        }

        searchResults = new LinkedList<>();

        for (String s : searchMap.keySet()) {
            if (s.toLowerCase().contains(term.toLowerCase())) {
                searchResults.add(searchMap.get(s));
                // System.out.println(s + " contains " + term + ", therefore " +
                // searchMap.get(s) + "is put into the list");
            }
        }

        for (TreeItem<NUINode> t : searchResults) {
            t.getValue().setHighlighting(true);
        }
    }

    /**
     * TODO
     */
    public void gotoNextSearchResult() {
        // TODO Auto-generated method stub

    }

    /**
     * TODO
     */
    public void gotoPreviousSearchResult() {
        // TODO Auto-generated method stub

    }

    /**
     * TODO
     * 
     * @author Stefan Pilot
     */
    private void initializeSearchMap() {
        searchMap = new HashMap<>();
        List<TreeItem<NUINode>> l = treeToList(proofTreeView.getRoot());
        for (TreeItem<NUINode> t : l)
            searchMap.put(t.getValue().getLabel(), t);

    }

    /**
     * TODO
     * 
     * @author Stefan Pilot
     * @param t
     * @return
     */
    private List<TreeItem<NUINode>> treeToList(TreeItem<NUINode> t) {
        if (t == null)
            throw new IllegalArgumentException();
        return treeToList(t, new LinkedList<TreeItem<NUINode>>());
    }

    /**
     * TODO
     * 
     * @author Stefan Pilot
     * @param t
     * @param l
     * @return
     */
    private List<TreeItem<NUINode>> treeToList(TreeItem<NUINode> t, List<TreeItem<NUINode>> l) {
        if (t == null || l == null)
            throw new IllegalArgumentException();

        l.add(t);
        if (!t.getChildren().isEmpty())
            for (TreeItem<NUINode> ti : t.getChildren())
                l.addAll(treeToList(ti, new LinkedList<TreeItem<NUINode>>()));

        return l;
    }
}
