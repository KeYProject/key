package de.uka.ilkd.key.nui.prooftree;

import java.lang.reflect.Field;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import com.sun.javafx.scene.control.skin.TreeViewSkin;
import com.sun.javafx.scene.control.skin.VirtualContainerBase;
import com.sun.javafx.scene.control.skin.VirtualFlow;
import com.sun.javafx.scene.control.skin.VirtualFlow.ArrayLinkedList;

import de.uka.ilkd.key.nui.ComponentFactory;
import de.uka.ilkd.key.nui.controller.NUIController;
import javafx.animation.PauseTransition;
import javafx.application.Platform;
import javafx.fxml.FXML;
import javafx.scene.Node;
import javafx.scene.control.Button;
import javafx.scene.control.TextField;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;
import javafx.scene.input.KeyCode;
import javafx.scene.layout.AnchorPane;
import javafx.scene.layout.VBox;
import javafx.util.Duration;

public class SearchHandler {
    
    private enum Direction {
        UP, DOWN
    }

    private boolean anythingIsHighlighted = false; //NOPMD

    /**
     * The VBox containing both the TreeView and the Anchor Pane where the
     * Search elements are
     */
    @FXML
    private final VBox mainVBox;
    /**
     * The Button toggling selectNextItem in searching
     */
    @FXML
    private Button nextButton;
    /**
     * The Button toggling selectPreviousItem in searching
     */
    @FXML
    private Button previousButton;
    
    /**
     * Weak-referenced Set of ProofTreeCells
     */
    private final Set<ProofTreeCell> proofTreeCells;
    
    private TreeView<NUINode> proofTreeView;
    /**
     * The TextField where search terms are entered
     */
    private TextField searchTextField;

    /**
     * The Anchor Pane holding the Search Field and its buttons
     */
    private AnchorPane searchViewAnchorPane;

    /**
     * A List representation of the all the TreeItems
     */
    private List<TreeItem<NUINode>> treeItems;

    /**
     * Displays a search view.
     * 
     * @param proofTreeView
     *            the proofTreeView to search in
     * @param proofTreeCells
     *            the ProofTreeCells to highlight the results in (use weak
     *            references!)
     * @param mainVBox
     *            the VBox to draw the interface in
     */
    public SearchHandler(TreeView<NUINode> proofTreeView, Set<ProofTreeCell> proofTreeCells, VBox mainVBox) {
        this.mainVBox = mainVBox;
        // this.searchMatches = searchMatches;
        this.proofTreeView = proofTreeView;
        this.proofTreeCells = proofTreeCells;

        // Loads the components from the .searchView fxml file
        searchViewAnchorPane = (AnchorPane) (new ComponentFactory("components/"))
                .createComponent(".searchView", ".searchView.fxml");

        // iterates over the previously loaded components and adds EventHandlers
        // to each of them
        for (Node n : searchViewAnchorPane.getChildren()) {
            if (n.getId().equals("previousButton")) {
                previousButton = (Button) n;
                previousButton.setOnAction((event) -> moveSelectionAndScrollIfNeeded(Direction.DOWN));
            }
            else if (n.getId().equals("nextButton")) {
                nextButton = (Button) n;
                nextButton.setOnAction((event) -> moveSelectionAndScrollIfNeeded(Direction.UP));
            }
            else if (n.getId().equals("searchTextField")) {
                searchTextField = (TextField) n;
                searchTextField.textProperty().addListener((obs, oldText, newText) -> {
                    nextButton.setDisable(newText.isEmpty());
                    previousButton.setDisable(newText.isEmpty());
                    if (newText.isEmpty()) {
                        proofTreeView.getRoot().getValue().resetSearch();
                    }
                    else {
                        anythingIsHighlighted = proofTreeView.getRoot().getValue().search(newText);
                    }
                });
                Platform.runLater(() -> searchTextField.requestFocus());
            }
        }

        // Register a Key Event Handler so that ENTER will trigger the
        // "Next"-Button and Shift-ENTER will trigger the "Previous"-Button
        NUIController.getInstance().registerKeyListener(KeyCode.ENTER, new KeyCode[] {},
                (event) -> {
                    if (event.isShiftDown()) {
                        previousButton.arm();
                        PauseTransition pause = new PauseTransition(Duration.millis(130));
                        pause.setOnFinished(e -> {
                            previousButton.disarm();
                        });
                        previousButton.fire();
                        pause.play();

                    }
                    else {
                        nextButton.arm();
                        PauseTransition pause = new PauseTransition(Duration.millis(130));
                        pause.setOnFinished(e -> {
                            nextButton.disarm();
                        });
                        nextButton.fire();
                        pause.play();

                    }
                });
        mainVBox.getChildren().add(searchViewAnchorPane);
    }

    /**
     * This routine <i>must</i> be called in order to actually remove the search
     * View from the interface (without any memory leaks).
     */
    public void destruct() {
        for (Iterator<Node> i = mainVBox.getChildren().iterator(); i.hasNext();) {
            final Node node = i.next();
            if (node == searchViewAnchorPane) { //NOPMD
                i.remove();
                break;
            }
        }
        NUIController.getInstance().unregisterKeyListener(KeyCode.ENTER);
        // searchMatches.clear();
        this.proofTreeView.getRoot().getValue().resetSearch();
        searchTextField = null;
        nextButton = null;
        previousButton = null;
        searchViewAnchorPane = null;
    }

    public void performFocusRequest() {
        searchTextField.requestFocus();
    }

    /**
     * TODO Bitte nicht löschen, in Code Reviews bitte ignorieren
     * @return
     */
    @SuppressWarnings("unchecked")
    private Set<ProofTreeCell> getProofTreeCells() {
        try {
            Field f = VirtualContainerBase.class.getDeclaredField("flow");
            f.setAccessible(true);
            Field g = VirtualFlow.class.getDeclaredField("cells");
            g.setAccessible(true);
            Set<ProofTreeCell> s = new HashSet<>();
            s.addAll((ArrayLinkedList<ProofTreeCell>) g.get(((VirtualFlow<ProofTreeCell>) f
                    .get(((TreeViewSkin<NUINode>) proofTreeView.skinProperty().get())))));
            return s;
        }
        catch (NoSuchFieldException e) {
            e.printStackTrace();
        }
        catch (SecurityException e) {
            e.printStackTrace();
        }
        catch (IllegalArgumentException e) {
            e.printStackTrace();
        }
        catch (IllegalAccessException e) {
            e.printStackTrace();
        }
        return null;
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
                 * 
                 * @param list
                 *            Where all the TreeItems are added to
                 * 
                 * @return <b>list</b>, but with all the TreeItems appended to
                 *         it
                 */

                private <T> List<TreeItem<T>> treeToList(final TreeItem<T> root,
                        final List<TreeItem<T>> list) {
                    if (root == null || list == null) {
                        throw new IllegalArgumentException();
                    }
                    list.add(root);
                    if (!root.getChildren().isEmpty()) {
                        for (TreeItem<T> ti : root.getChildren()) {
                            list.addAll(treeToList(ti, new LinkedList<TreeItem<T>>()));
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
     * Selects the next/previous item in searchMatches. Scrolls the
     * ProofTreeView if that item is not visible to the user. Expands the
     * ProofTreeView as needed. Only to be used together with
     * <tt>TreeViewController.search()</tt>.
     * 
     * @param moveDownwards
     *            whether the selection is to be moved up- or downwards
     */
    private void moveSelectionAndScrollIfNeeded(Direction direction) {
        if (!anythingIsHighlighted) {
            return;
        }

        List<TreeItem<NUINode>> treeItems = getTreeItems();
        // catch bad calls
        // if (searchMatches == null || searchMatches.isEmpty())
        // return;

        final TreeItem<NUINode> currentlySelectedItem = proofTreeView.getSelectionModel()
                .getSelectedItem();

        TreeItem<NUINode> itemToSelect = null;

        // Basically does: itemToSelect = currentlySelectedItem + 1
        if (currentlySelectedItem == null
                || direction == Direction.UP
                        && (treeItems.indexOf(currentlySelectedItem) == treeItems.size() - 1)
                || direction == Direction.DOWN && (treeItems.indexOf(currentlySelectedItem) == 0)) {
            if (direction == Direction.UP) {
                itemToSelect = treeItems.get(0);
            }
            else {
                itemToSelect = treeItems.get(treeItems.size() - 1);
            }
        }
        else {
            if (direction == Direction.UP) {
                itemToSelect = treeItems.get(treeItems.indexOf(currentlySelectedItem) + 1);
            }
            else {
                itemToSelect = treeItems.get(treeItems.indexOf(currentlySelectedItem) - 1);
            }
        }

        // Basically does: while(!searchMatches.contains(itemToSelect))
        // itemToSelect++;
        while (!itemToSelect.getValue().isSearchResult()) {
            if ((direction == Direction.UP && (treeItems.indexOf(itemToSelect) == treeItems.size() - 1))
                    || (direction == Direction.DOWN && (treeItems.indexOf(itemToSelect) == 0))) {
                itemToSelect = direction == Direction.UP ? treeItems.get(0)
                        : treeItems.get(treeItems.size() - 1);
            }
            else {
                itemToSelect = direction == Direction.UP ? treeItems.get(treeItems.indexOf(itemToSelect) + 1)
                        : treeItems.get(treeItems.indexOf(itemToSelect) - 1);
            }
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
        boolean performScroll = true;
        for (ProofTreeCell c : getProofTreeCells()) {
            if (c.getTreeItem() == itemToSelect) {
                performScroll = false;
                break;
            }
        }

        if (performScroll)
            // if we are to scroll downwards, we have to subtract an offset to
            // make
            // the selected item appear in middle.
            proofTreeView.scrollTo(proofTreeView.getSelectionModel().getSelectedIndex()
                    - (direction == Direction.UP ? 0 : (int) (proofTreeCells.size() / 2)));
    }
}
