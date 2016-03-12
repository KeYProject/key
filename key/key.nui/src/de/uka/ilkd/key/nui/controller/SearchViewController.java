package de.uka.ilkd.key.nui.controller;

import java.lang.reflect.Field;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import com.sun.javafx.scene.control.skin.TreeViewSkin;
import com.sun.javafx.scene.control.skin.VirtualContainerBase;
import com.sun.javafx.scene.control.skin.VirtualFlow;
import com.sun.javafx.scene.control.skin.VirtualFlow.ArrayLinkedList;

import de.uka.ilkd.key.nui.prooftree.NUINode;
import de.uka.ilkd.key.nui.prooftree.ProofTreeCell;
import javafx.animation.PauseTransition;
import javafx.application.Platform;
import javafx.fxml.FXML;
import javafx.scene.control.Button;
import javafx.scene.control.TextField;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;
import javafx.scene.input.KeyCode;
import javafx.scene.layout.Pane;
import javafx.util.Duration;

public class SearchViewController extends NUIController {

    private enum Direction {
        UP, DOWN
    }

    private int numberOfSearchResults = 0;

    /**
     * The Button toggling selectNextItem in searching
     */
    @FXML
    private Button btnSearchNext;
    /**
     * The Button toggling selectPreviousItem in searching
     */
    @FXML
    private Button btnSearchPrev;

    /**
     * A click on this Button closes the SearchView
     */
    @FXML
    private Button btnCloseSearchView;

    /**
     * The TextField where search terms are entered
     */
    @FXML
    private TextField tfSearchQuery;

    /**
     * Weak-referenced Set of ProofTreeCells
     */
    private Set<ProofTreeCell> proofTreeCells;

    /**
     * Reference of TreeView
     */
    private TreeView<NUINode> proofTreeView;
    /**
     * Reference of Parent Connection between TreeView and SearchView
     */
    private Pane treeViewPane;

    /**
     * The Anchor Pane holding the Search Field and its buttons
     */
    @FXML
    private Pane searchViewPane;

    /**
     * A List representation of the all the TreeItems
     */
    private List<TreeItem<NUINode>> treeItems;

    /**
     * Set TreeView used for the search
     * 
     * @param proofTreeView
     *            reference to treeView
     * @param proofTreeCells
     *            reference to cells of treeView
     * @param treeViewPane
     *            reference to treeViewPane(Parent of searchView)
     */
    public void initSearch(TreeView<NUINode> proofTreeView,
            Set<ProofTreeCell> proofTreeCells, Pane treeViewPane) {

        this.proofTreeView = proofTreeView;
        this.proofTreeCells = proofTreeCells;
        this.treeViewPane = treeViewPane;

        Platform.runLater(() -> tfSearchQuery.requestFocus());
    }

    public void performFocusRequest() {
        tfSearchQuery.requestFocus();
    }

    /**
     * TODO Bitte nicht löschen, in Code Reviews bitte ignorieren
     * 
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
            s.addAll((ArrayLinkedList<ProofTreeCell>) g
                    .get(((VirtualFlow<ProofTreeCell>) f
                            .get(((TreeViewSkin<NUINode>) proofTreeView
                                    .skinProperty().get())))));
            return s;
        }
        catch (NoSuchFieldException e) {
            e.printStackTrace();// TODO
        }
        catch (SecurityException e) {
            e.printStackTrace();// TODO
        }
        catch (IllegalArgumentException e) {
            e.printStackTrace();// TODO
        }
        catch (IllegalAccessException e) {
            e.printStackTrace();// TODO
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
                            list.addAll(treeToList(ti,
                                    new LinkedList<TreeItem<T>>()));
                        }
                    }
                    return list;
                }
            }
            treeItems = (new TreeToListHelper()).treeToList(
                    proofTreeView.getRoot(),
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
        if (numberOfSearchResults<1) {
            return;
        }

        List<TreeItem<NUINode>> treeItems = getTreeItems();
        // catch bad calls
        // if (searchMatches == null || searchMatches.isEmpty())
        // return;

        final TreeItem<NUINode> currentlySelectedItem = proofTreeView
                .getSelectionModel().getSelectedItem();

        TreeItem<NUINode> itemToSelect = null;

        // Basically does: itemToSelect = currentlySelectedItem + 1
        if (currentlySelectedItem == null
                || direction == Direction.UP && (treeItems
                        .indexOf(currentlySelectedItem) == treeItems.size() - 1)
                || direction == Direction.DOWN
                        && (treeItems.indexOf(currentlySelectedItem) == 0)) {
            if (direction == Direction.UP) {
                itemToSelect = treeItems.get(0);
            }
            else {
                itemToSelect = treeItems.get(treeItems.size() - 1);
            }
        }
        else {
            if (direction == Direction.UP) {
                itemToSelect = treeItems
                        .get(treeItems.indexOf(currentlySelectedItem) + 1);
            }
            else {
                itemToSelect = treeItems
                        .get(treeItems.indexOf(currentlySelectedItem) - 1);
            }
        }

        // Basically does: while(!searchMatches.contains(itemToSelect))
        // itemToSelect++;
        while (!itemToSelect.getValue().isSearchResult()) {
            if ((direction == Direction.UP && (treeItems
                    .indexOf(itemToSelect) == treeItems.size() - 1))
                    || (direction == Direction.DOWN
                            && (treeItems.indexOf(itemToSelect) == 0))) {
                itemToSelect = direction == Direction.UP ? treeItems.get(0)
                        : treeItems.get(treeItems.size() - 1);
            }
            else {
                itemToSelect = direction == Direction.UP
                        ? treeItems.get(treeItems.indexOf(itemToSelect) + 1)
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
            proofTreeView.scrollTo(
                    proofTreeView.getSelectionModel().getSelectedIndex()
                            - (direction == Direction.UP ? 0
                                    : (int) (proofTreeCells.size() / 2)));
    }

    @Override
    protected void init() {
        btnSearchPrev.setOnAction(
                (event) -> moveSelectionAndScrollIfNeeded(Direction.DOWN));
        btnSearchNext.setOnAction(
                (event) -> moveSelectionAndScrollIfNeeded(Direction.UP));
        btnCloseSearchView.setOnAction((event) -> closeSearchView());
        tfSearchQuery.textProperty().addListener((obs, oldText, newText) -> {
            btnSearchNext.setDisable(newText.isEmpty());
            btnSearchPrev.setDisable(newText.isEmpty());
            if (newText.isEmpty()) {
                proofTreeView.getRoot().getValue().resetSearch();
                nui.updateStatusbar("");
            }
            else {
                numberOfSearchResults = proofTreeView.getRoot().getValue()
                        .search(newText);

                nui.updateStatusbar(
                        "Number of Search Results: " + numberOfSearchResults);

                if (numberOfSearchResults == 0) {
                    // adds the style class for no search results
                    tfSearchQuery.getStyleClass().add("search-noResults");
                }
                else {
                    // removes the style class for no search results
                    tfSearchQuery.getStyleClass()
                            .removeIf((e) -> e.equals("search-noResults"));
                }
            }
        });

        searchViewPane.setOnKeyPressed((e) -> {
            if (KeyCode.ESCAPE == e.getCode()) {
                closeSearchView();
            }
            else if (KeyCode.ENTER == e.getCode()) {
                PauseTransition pause = new PauseTransition(
                        Duration.millis(130));
                Button button;
                button = e.isShiftDown() ? btnSearchPrev : btnSearchNext;
                button.arm();
                pause.setOnFinished(event -> {
                    button.disarm();
                });
                button.fire();
                pause.play();
            }
        });

        // Assign stylesheet
        searchViewPane.getStylesheets().add(getClass()
                .getResource("../components/searchView.css").toExternalForm());
    }

    private void closeSearchView() {
        // delete searchView component form treeViewPane
        treeViewPane.getChildren().remove(searchViewPane);
        // reset proofTreeView
        proofTreeView.getRoot().getValue().resetSearch();

        tfSearchQuery.setText("");
    }
}
