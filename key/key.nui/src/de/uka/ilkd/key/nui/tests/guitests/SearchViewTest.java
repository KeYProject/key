package de.uka.ilkd.key.nui.tests.guitests;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.stream.Collectors;

import org.junit.Test;

import de.uka.ilkd.key.nui.TreeViewState;
import de.uka.ilkd.key.nui.controller.TreeViewController;
import de.uka.ilkd.key.nui.exceptions.ControllerNotFoundException;
import de.uka.ilkd.key.nui.prooftree.NUINode;
import de.uka.ilkd.key.nui.prooftree.ProofTreeItem;
import javafx.collections.ObservableList;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.TextField;
import javafx.scene.input.KeyCodeCombination;
import javafx.scene.input.KeyCombination;
import javafx.scene.layout.HBox;

/**
 * Test for User Story. - #14469 Suchen im Beweisbaum - #15081 Rueckmeldung im
 * Falle keiner Suchergebnisse
 * 
 * @author Florian Breitfelder
 *
 */

@SuppressWarnings("PMD.AtLeastOneConstructor")
// PMD will also complain if adding the constructor, then saying "avoid useless
// constructors"
public class SearchViewTest extends NUITestHelper {

    public int numberOfResults = 0;

    /**
     * Test for searching in the tree by invoking the search with CTRL+F.
     */
    @Test
    public void usingSearchByControlF() {
        // load prooffile example01.proof
        this.loadProof("example01.proof", false);

        // expand tree
        this.rightClickOn("Proof Tree ");
        this.clickOn("Expand All");

        // open searchView by pressing ctrl+f
        this.push((KeyCodeCombination) KeyCombination.keyCombination("Ctrl+F"));

        this.checkSearchResult("no matches!", "Number of Search Results: 0");
        this.checkSearchResult("case", "Number of Search Results: 14");
        this.checkSearchResult("closed", "Number of Search Results: 15");
    }

    /**
     * Test for searching in the tree by invoking the search with the context
     * menu.
     */
    @Test
    public void usingSearchByContextMenu() {
        // load prooffile example01.proof
        this.loadProof("example01.proof", false);

        // expand tree
        this.rightClickOn("Proof Tree ");
        this.clickOn("Expand All");

        // open searchView via contextmenu
        this.rightClickOn("Proof Tree ");
        this.clickOn("Search");

        this.checkSearchResult("no matches!", "Number of Search Results: 0");
        this.checkSearchResult("and", "Number of Search Results: 22");
        this.checkSearchResult("or", "Number of Search Results: 31");
    }

    /**
     * Checks if the number of search results matches.
     * 
     * @param searchText
     *            The text searched for.
     * @param resultStatusBar
     *            The string shown in the status bar after searching.
     */
    private void checkSearchResult(final String searchText,
            final String resultStatusBar) {
        // select current searchtext to overwrite it
        this.push((KeyCodeCombination) KeyCombination.keyCombination("Ctrl+A"));

        this.write(searchText);

        final Label label = ((Label) find("#statustext"));
        // Loading process was canceled
        assertTrue(label.getText().equals(resultStatusBar));
    }

    /**
     * Test for searching in the tree by invoking the search with the context
     * menu.
     */
    @Test
    public void checkTreeItems() {
        TreeViewState treeViewState = null;
        ProofTreeItem rootProofTreeItem = null;

        // load prooffile example01.proof
        this.loadProof("example01.proof", false);

        // expand tree
        this.rightClickOn("Proof Tree ");
        this.clickOn("Expand All");

        // open searchView via contextmenu
        this.rightClickOn("Proof Tree ");
        this.clickOn("Search");

        this.checkSearchResult("no matches!", "Number of Search Results: 0");

        // Load model
        treeViewState = dataModel.getLoaddTriVwStat();
        rootProofTreeItem = treeViewState.getTreeItem();

        // walk through the tree
        assertEquals(0,
                checkTreeItemsSearchResult(rootProofTreeItem, "no matches!"));

        this.checkSearchResult("and", "Number of Search Results: 22");

        // Load model
        treeViewState = dataModel.getLoaddTriVwStat();
        rootProofTreeItem = treeViewState.getTreeItem();

        // walk through the tree
        assertEquals(22, checkTreeItemsSearchResult(rootProofTreeItem, "and"));

        this.checkSearchResult("or", "Number of Search Results: 31");

        // Load model
        treeViewState = dataModel.getLoaddTriVwStat();
        rootProofTreeItem = treeViewState.getTreeItem();

        // walk through the tree
        assertEquals(31, checkTreeItemsSearchResult(rootProofTreeItem, "or"));
    }

    /**
     * Used to check if every tree item which contains the searchText is
     * highlighted.
     * 
     * @param proofTreeItem
     *            root of current subtree
     * @param searchText
     * @return number of search results
     */
    private int checkTreeItemsSearchResult(ProofTreeItem proofTreeItem,
            final String searchText) {
        this.numberOfResults = 0;

        treeDown(proofTreeItem, searchText);

        return this.numberOfResults;
    }

    /**
     * Used to walk through the tree recursively. Only for
     * checkTreeItemsSearchResult
     * 
     * @param proofTreeItem
     */
    private void treeDown(ProofTreeItem proofTreeItem,
            final String searchText) {
        for (int i = 0; i < proofTreeItem.getInternalChildren().size(); i++) {
            NUINode nuiNode = proofTreeItem.getInternalChildren().get(i)
                    .getValue();
            if (nuiNode.getLabel().toString().contains(searchText)) {
                assertTrue(nuiNode.isSearchResult());
                numberOfResults++;
            }
            treeDown(proofTreeItem.getInternalChildren().get(i), searchText);
        }
    }

    /**
     * Tests if search text field is highlighted if there are no search results
     * 
     * @throws ControllerNotFoundException
     */
    @Test
    public void checkHighlightedNoResults() throws ControllerNotFoundException {
        TreeViewController treeViewController = (TreeViewController) nui
                .getController("treeViewPane");

        // load prooffile example01.proof
        this.loadProof("example01.proof", false);

        // expand tree
        this.rightClickOn("Proof Tree ");
        this.clickOn("Expand All");

        // open searchView via contextmenu
        this.rightClickOn("Proof Tree ");
        this.clickOn("Search");

        this.checkSearchResult("and", "Number of Search Results: 22");
        assertFalse(SearchViewTest.highlightedNoResults(
                treeViewController.getSearchViewPane().getChildren()));

        this.checkSearchResult("no matches!", "Number of Search Results: 0");
        assertTrue(SearchViewTest.highlightedNoResults(
                treeViewController.getSearchViewPane().getChildren()));

        this.checkSearchResult("or", "Number of Search Results: 31");
        assertFalse(SearchViewTest.highlightedNoResults(
                treeViewController.getSearchViewPane().getChildren()));
    }

    /**
     * Tests scrolling through search results
     * 
     * @throws ControllerNotFoundException
     * 
     */
    @Test
    public void testScrollingThroughResults()
            throws ControllerNotFoundException {
        TreeViewController treeViewController = (TreeViewController) nui
                .getController("treeViewPane");

        String[] cells = { "0: andRight", "1: andRight", "3: andRight",
                "10: concrete_and_3", "43: concrete_and_2",
                "11: concrete_and_4", "62: concrete_and_2", "8: andLeft",
                "79: concrete_and_2", "83: concrete_and_2",
                "112: concrete_and_2", "141: concrete_and_2",
                "210: concrete_and_2", "256: concrete_and_1",
                "298: concrete_and_2", "327: concrete_and_2",
                "385: concrete_and_2", "412: concrete_and_1",
                "491: concrete_and_1", "514: concrete_and_1",
                "601: concrete_and_2", "666: concrete_and_2" };
        // load prooffile example01.proof
        this.loadProof("example01.proof", false);

        // expand tree
        this.rightClickOn("Proof Tree ");
        this.clickOn("Expand All");

        // open searchView via contextmenu
        this.rightClickOn("Proof Tree ");
        this.clickOn("Search");

        // check statusbar
        this.checkSearchResult("and", "Number of Search Results: 22");
        assertFalse(SearchViewTest.highlightedNoResults(
                treeViewController.getSearchViewPane().getChildren()));

        // scroll through search results forward
        for (int i = 0; i < 22; i++) {
            clickOn(">");
            assertEquals(cells[i], treeViewController.getProofTreeCells()
                    .stream().filter((cell) -> cell.isSelected())
                    .collect(Collectors.toList()).get(0).getItem().getLabel());
        }

        // scroll through search results backwards
        for (int i = 20; i >= 0; i--) {
            clickOn("<");
            assertEquals(cells[i], treeViewController.getProofTreeCells()
                    .stream().filter((cell) -> cell.isSelected())
                    .collect(Collectors.toList()).get(0).getItem().getLabel());
        }
    }

    /**
     * Test to close the search view via button "X"
     */
    @Test
    public void testCloseSearchViewButtonX() {
        // load prooffile example01.proof
        this.loadProof("example01.proof", false);

        // expand tree
        this.rightClickOn("Proof Tree ");
        this.clickOn("Expand All");

        // check if search view is not loaded
        assertTrue((HBox) find("#searchViewPane") == null);

        // open searchView via contextmenu
        this.rightClickOn("Proof Tree ");
        this.clickOn("Search");

        // check if search view is open
        assertTrue(((HBox) find("#searchViewPane")).isVisible());

        // close search view
        clickOn("X");

        // check if search view is closed
        assertTrue((HBox) find("#searchViewPane") == null);

        // open search view by pressing ctrl+f
        this.push((KeyCodeCombination) KeyCombination.keyCombination("Ctrl+F"));

        // check if search view is open
        assertTrue(((HBox) find("#searchViewPane")).isVisible());

        // close search view
        clickOn("X");

        // check if search view is closed
        assertTrue((HBox) find("#searchViewPane") == null);
    }

    /**
     * checks if search query text field is highlighted
     * 
     * @param children
     *            list of nodes. Must contain text field tfSearchQuery
     * 
     * @return true if tfSearchQuery is highlighted
     */
    private static boolean highlightedNoResults(ObservableList<Node> children) {
        for (Node node : children) {
            if (node.getId().equals("tfSearchQuery")
                    && node instanceof TextField) {
                TextField tfSearchQuery = (TextField) node;
                return tfSearchQuery.getStyleClass()
                        .contains("search-noResults");
            }
        }
        return false;
    }

}
