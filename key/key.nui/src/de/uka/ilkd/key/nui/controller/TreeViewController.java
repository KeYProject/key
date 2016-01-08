package de.uka.ilkd.key.nui.controller;

import java.io.File;
import java.net.URL;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.ResourceBundle;
import java.util.stream.Collectors;

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
     * stores reference to 'this' for singleton purpose TODO this is bad
     * practice
     * 
     * @author Stefan Pilot
     */
    private static TreeViewController instance;

    /**
     * Initialization method for scene; loads the default proof
     */
    @Override
    public void initialize(URL location, ResourceBundle resources) {

        instance = this; // TODO this is bad practice

        // set cell factory for rendering cells
        proofTreeView.setCellFactory(
                new Callback<TreeView<NUINode>, TreeCell<NUINode>>() {
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
        String cssPath = this.getClass()
                .getResource("../components/treeView.css").toExternalForm();
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
            KeYEnvironment<?> environment = KeYEnvironment.load(
                    JavaProfile.getDefaultInstance(), proofFile, null, null,
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
     * returns reference to 'this' TODO remove this singleton, it is bad
     * practice
     * 
     * @author Stefan Pilot
     */
    static TreeViewController getInstance() {
        return instance;
    }

    /**
     * stores all the Labels in the tree and their respective TreeItems must be
     * initialized with initializeSearchMap()
     */
    private HashMap<String, TreeItem<NUINode>> searchMap;

    /**
     * After a call to search(String term), this stores all the TreeItems found
     * by that search. At every point in time, All of these TreeItems are
     * currently highlighted.
     */
    private List<TreeItem<NUINode>> searchResults;

    /**
     * This will highlight all the TreeItems for which <tt>.contains(term)</tt>
     * is <tt>true</tt>. The search is not case sensitive.
     * 
     * @param term
     *            The String to search for
     */
    public boolean search(String term) {
        if (searchMap == null)
            initializeSearchMap();

        if (searchResults != null)
            for (TreeItem<NUINode> t : searchResults)
                t.getValue().setHighlighting(false);

        searchResults = new LinkedList<>();

        for (String s : searchMap.keySet())
            if (s.toLowerCase().contains(term.toLowerCase()))
                searchResults.add(searchMap.get(s));

        if (!searchResults.isEmpty()) {
            for (TreeItem<NUINode> t : searchResults) {
                t.getValue().setHighlighting(true);
                ProofTreeActions.refeshTreeItem(t);
            }
            gotoNextSearchResult();
            return true;
        }
        else
            return false;
    }

    /**
     * TODO someday this will move the focus to the next found item
     */
    public void gotoNextSearchResult() {

        // check if match list is empty
        if (searchResults.isEmpty())
            return;

        // the current selected index
        int idxSelected = proofTreeView.getSelectionModel().getSelectedIndex();

        // get next higher index and its tree node
        // TODO can be very much improved using your grips
        // store list of indices of matches
        List<Integer> idxOfMatches = new LinkedList<>();
        for (TreeItem<NUINode> i : searchResults) {
            int idx = proofTreeView.getRow(i);
            idxOfMatches.add(idx);
            System.out.print(idx + " ");
        }
        System.out.println();

        // select the next largest match index.
        // if there is no, choose match with smallest index.
        int nextLargerIdx;
        List<Integer> listLargerThanSelected = idxOfMatches.stream()
                .filter(s -> s > idxSelected).collect(Collectors.toList());
        if (!listLargerThanSelected.isEmpty()) {
            // TODO Can be done very much smarter i guess
            nextLargerIdx = listLargerThanSelected.stream()
                    .min(Comparator.comparingInt(i -> i)).get();
        }
        else {
            // TODO not the smartest way...
            nextLargerIdx = idxOfMatches.stream()
                    .min(Comparator.comparingInt(i -> i)).get();
        }

        // TODO this is very inefficient
        // Problem is that you can't get the TreeItem by index by
        // proofTreeView.getTreeItem(row) if parents of the treeItem
        // are collapsed
        int idxInList = idxOfMatches.indexOf(nextLargerIdx);
        TreeItem<NUINode> nextLargerTI = searchResults.get(idxInList);

        // expand all parents so we can reach the treeItem
        // TODO this is also not very smartly done and coudl be refactored
        // in a recurive method. However, if you change the lines before
        // this could be superfluous.
        TreeItem<NUINode> parent = nextLargerTI;
        while (parent.getParent() != null) {
            parent = parent.getParent();
            parent.setExpanded(true);
        }

        // scrolling and selecting
        proofTreeView.scrollTo(nextLargerIdx);
        proofTreeView.getSelectionModel().select(nextLargerIdx);

        System.out.println("Currently Selected: " + idxSelected
                + ", Next Match at " + nextLargerIdx);

    }

    /**
     * TODO someday this will move the focus to the previous found item
     */
    public void gotoPreviousSearchResult() {
        // TODO Auto-generated method stub

    }

    /**
     * This will recursively parse the proof tree and store all elements in the
     * <tt>searchMap</tt>
     */
    private void initializeSearchMap() {
        searchMap = new HashMap<>();
        List<TreeItem<NUINode>> l = treeToList(proofTreeView.getRoot());
        for (TreeItem<NUINode> t : l)
            searchMap.put(t.getValue().getLabel(), t);

    }

    /**
     * Parses a Tree, beginning at <b>t</b>, and puts every TreeItem into a
     * List. This should rarely be called directly.
     * 
     * @param t
     *            Where to start parsing the tree
     * @return A List containing all TreeItems who are children of <b>t</b> or
     *         of its children
     */
    private List<TreeItem<NUINode>> treeToList(TreeItem<NUINode> t) {
        if (t == null)
            throw new IllegalArgumentException();
        return treeToList(t, new LinkedList<TreeItem<NUINode>>());
    }

    /**
     * Parses a Tree, beginning at <b>t</b>, and adds to list every TreeItem
     * that is a child of <b>root</b> or of its children <b>l</b>. This should
     * rarely be called directly.
     * 
     * @param root
     *            Where to start parsing
     * @param list
     *            Where all the TreeItems are added to
     * @return <b>list</b>, but with all the TreeItems appended to it
     */
    private List<TreeItem<NUINode>> treeToList(TreeItem<NUINode> root,
            List<TreeItem<NUINode>> list) {
        if (root == null || list == null)
            throw new IllegalArgumentException();

        list.add(root);
        if (!root.getChildren().isEmpty())
            for (TreeItem<NUINode> ti : root.getChildren())
                list.addAll(
                        treeToList(ti, new LinkedList<TreeItem<NUINode>>()));

        return list;
    }
}
