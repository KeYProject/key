package de.uka.ilkd.key.nui.controller;

import java.io.File;
import java.net.URL;
import java.util.LinkedList;
import java.util.List;
import java.util.ResourceBundle;
import java.util.WeakHashMap;
import java.util.concurrent.Callable;

import com.sun.xml.internal.org.jvnet.staxex.NamespaceContextEx.Binding;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nui.ComponentFactory;
import de.uka.ilkd.key.nui.IconFactory;
import de.uka.ilkd.key.nui.NUI;
import de.uka.ilkd.key.nui.controller.NUIController.Place;
import de.uka.ilkd.key.nui.prooftree.NUINode;
import de.uka.ilkd.key.nui.prooftree.ProofTreeCell;
import de.uka.ilkd.key.nui.prooftree.ProofTreeVisualizer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import javafx.application.Platform;
import javafx.beans.binding.Bindings;
import javafx.beans.binding.DoubleBinding;
import javafx.beans.binding.ObjectBinding;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.beans.value.WeakChangeListener;
import javafx.collections.FXCollections;
import javafx.collections.MapChangeListener;
import javafx.collections.ObservableList;
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
    public static final String NAME = "treeView";

    /**
     * The IconFactory used to create icons for the proof tree nodes.
     */
    private final IconFactory icf;

    /**
     * A <tt>WeakHashMap</tt> storing the <tt>ProofTreeCells</tt> currently
     * existing.
     */
    private WeakHashMap<ProofTreeCell, DoubleBinding> proofTreeCells = new WeakHashMap<>();

    /**
     * The proofTree view of the GUI.
     */
    @FXML
    private TreeView<NUINode> proofTreeView;

    /**
     * An ObservableList storing the Items matching a <tt/>search()<tt/>
     */
    private ObservableList<TreeItem<NUINode>> searchMatches = FXCollections
            .observableList(new LinkedList<TreeItem<NUINode>>());

    private List<TreeItem<NUINode>> treeItems;

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

            // Look for changes to TreeViews Place. If changed and searchView is
            // visible, also change searchView's Place.
            NUIController.getInstance().getPlaceComponent()
                    .addListener(new MapChangeListener<String, Place>() {
                @Override
                public void onChanged(Change<? extends String, ? extends Place> change) {
                    if (change.getKey().equals(NAME) && NUIController.getInstance()
                            .getPlaceComponent().containsKey(SearchViewController.NAME)) {
                        NUIController.getInstance().createOrMoveOrHideComponent(
                                SearchViewController.NAME, change.getValueAdded(),
                                SearchViewController.RESOURCE);
                    }
                }
            });

            // Register KeyEvent
            NUIController.getInstance().registerKeyListener(KeyCode.F,
                    new KeyCode[] { KeyCode.CONTROL }, (event) -> {
                if (NUIController.getInstance().getPlaceComponent().containsKey(NAME)) {
                    try {
                        NUIController.getInstance().createOrMoveOrHideComponent(
                                SearchViewController.NAME,
                                NUIController.getInstance().getPlaceComponent().get(NAME),
                                SearchViewController.RESOURCE);
                    }
                    catch (IllegalArgumentException ex) {
                        // SearchView already exists
                        SearchViewController c = ComponentFactory.getInstance()
                                .getController(SearchViewController.NAME);
                        c.performFocusRequest();
                    }
                }
            });

            NUIController.getInstance().registerKeyListener(KeyCode.ESCAPE, null, (event) -> {
                NUIController.getInstance().createOrMoveOrHideComponent(SearchViewController.NAME,
                        Place.HIDDEN, SearchViewController.RESOURCE);
                searchMatches.clear();
            });
        });

        // set cell factory for rendering cells
        proofTreeView.setCellFactory((treeItem) -> {
            ProofTreeCell c = new ProofTreeCell(icf, searchMatches);
            Platform.runLater(() -> registerTreeCell(c));
            return c;
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
     * Loads and displays a file containing a KeY proof. May fail and/or throw
     * various exceptions if the file does not exist or does not contain a valid
     * proof.
     * 
     * @param file
     *            The proof file to load.
     */
    public final void loadAndDisplayProof(File file) {
        displayProof(loadProof(file));
        searchMatches.clear();
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
        searchMatches.clear();
    }

    /**
     * This method should be called every time a new TreeCell is being created.
     * <tt>this</tt> will reference the ProofTreeCell in a WeakHandle in order
     * to find out which TreeItems currently are visible to the user.
     *
     * @param t
     *            the ProofTreeCell to register.
     */
    private void registerTreeCell(ProofTreeCell t) {
        proofTreeCells.put(t,
                Bindings.createDoubleBinding(() -> t.getHeight(), t.heightProperty()));
    }

    /**
     * Searches the <tt>Label</tt>s of the <tt>TreeItems</tt> in the underlying
     * <tt>ProofTree</tt> for a given term. Highlights all the matches.<br/>
     * It is possible to use this for an incremental search, but doing so is
     * inefficient because the list storing the matches from the last search is
     * being emptied on every call. <br/>
     * <br/>
     * <b><tt>TODO</tt> optimize this for incremental search by buffering the
     * last search term.</b>
     * 
     * @param term
     *            The String to search for.
     */
    public final void search(String term) {
        // remove old matches
        searchMatches.clear();
        // exit if no search term specified
        if (term.isEmpty())
            return;

        // iterate over all the TreeItems and add them to searchMatches if they
        // match the search
        for (TreeItem<NUINode> t : getTreeItems()) {
            if (t.getValue().getLabel().toLowerCase().contains(term.toLowerCase())) {
                searchMatches.add(t);
            }
        }
    }

    /**
     * Selects the next item in searchMatches. Scrolls the ProofTreeView if that
     * item is not visible to the user. Expands the ProofTreeView as needed.
     * Only to be used together with <tt>TreeViewController.search()</tt>.
     */
    public void selectAndIfNeededScrollToNextSearchResult() {
        // catch bad calls
        if (searchMatches.isEmpty() || searchMatches == null)
            return;

        TreeItem<NUINode> currentlySelectedItem = proofTreeView.getSelectionModel()
                .getSelectedItem();
        TreeItem<NUINode> itemToSelect;

        /*
         * start from the top if a) no item is selected b) an item is selected
         * that is not a search result c) the selected item is the last search
         * result
         */
        if (currentlySelectedItem == null || !searchMatches.contains(currentlySelectedItem)
                || searchMatches.size() == searchMatches.indexOf(currentlySelectedItem) + 1) {
            itemToSelect = searchMatches.get(0);
        }
        else {
            itemToSelect = searchMatches.get(searchMatches.indexOf(currentlySelectedItem) + 1);
        }
        // if the treeItem is not in an expanded branch of the tree, the tree
        // must be expanded accordingly
        if (proofTreeView.getRow(itemToSelect) == -1) {
            for (TreeItem<NUINode> t = itemToSelect; t.getParent() != null
                    && !t.getParent().isExpanded(); t = t.getParent()) {
                t.setExpanded(true);
            }
        }

        // select the item
        proofTreeView.getSelectionModel().select(itemToSelect);

        // if none of the treeCells contain the item we have just selected,
        // we need to scroll to make it visible
        if (proofTreeCells.keySet().stream().noneMatch(x -> (x.getTreeItem() == itemToSelect))) {
            proofTreeView.scrollTo(proofTreeView.getSelectionModel().getSelectedIndex());
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
     * Recursively walks through the tree, storing all items in the List being
     * returned
     * 
     * @return a List of all the TreeItems in the underlying ProofTreeView
     */
    private List<TreeItem<NUINode>> getTreeItems() {
        if (treeItems == null) {
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
                 * @return <b>list</b>, but with all the TreeItems appended to
                 *         it
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
            treeItems = (new TreeToListHelper()).treeToList(proofTreeView.getRoot(),
                    new LinkedList<TreeItem<NUINode>>());
        }

        return treeItems;
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
}
