package de.uka.ilkd.key.nui.tests.guitests;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import javafx.scene.control.Label;
import javafx.scene.input.KeyCodeCombination;
import javafx.scene.input.KeyCombination;

/**
 * Test for User Story. (005) Suchen im Beweisbaum #14469
 * 
 * Basic tests for treeView Component.
 * 
 * @author Florian Breitfelder
 *
 */
public class SearchViewTest extends NUITest {

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
    public void usingSearchByContextMenu() throws InterruptedException {
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

}
