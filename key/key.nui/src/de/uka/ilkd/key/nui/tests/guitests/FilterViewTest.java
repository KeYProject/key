package de.uka.ilkd.key.nui.tests.guitests;

import static org.junit.Assert.assertTrue;

import org.junit.Test;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCodeCombination;
import javafx.scene.input.KeyCombination;
import javafx.scene.layout.HBox;

public class FilterViewTest extends NUITest {

    @Test
    public void usingFilterByControlG() {
        // load prooffile example01.proof
        this.loadProof("example01.proof", false);

        // expand tree
        this.rightClickOn("Proof Tree ");
        this.clickOn("Expand All");

        // check if filter view is not loaded
        assertTrue((HBox) find("#filterViewHBox") == null);

        // open filterView by pressing ctrl+g
        this.push((KeyCodeCombination) KeyCombination.keyCombination("Ctrl+G"));

        // check if filter view is open
        assertTrue(((HBox) find("#filterViewHBox")).isVisible());

        // close filterView
        clickOn("X");

        // check if filter view is closed
        assertTrue((HBox) find("#filterViewHBox") == null);

        // open filterView by pressing ctrl+g again
        this.push((KeyCodeCombination) KeyCombination.keyCombination("Ctrl+G"));

        // close filter view with ESC
        this.press(KeyCode.ESCAPE);

        // check if filter view is closed
        assertTrue((HBox) find("#filterViewHBox") == null);

        // open filterView by pressing ctrl+g again
        this.push((KeyCodeCombination) KeyCombination.keyCombination("Ctrl+G"));

        // check if filter view is open again
        assertTrue(((HBox) find("#filterViewHBox")).isVisible());

        // filter
        enterFilterText("and");

        // disable filter
        clickOn("F");

        // enable filter
        clickOn("F");
    }

    @Test
    public void usingFilterByContextmenu() {
        // load prooffile example01.proof
        this.loadProof("example01.proof", false);

        // expand tree
        this.rightClickOn("Proof Tree ");
        this.clickOn("Expand All");

        // check if filter view is not loaded
        assertTrue((HBox) find("#filterViewHBox") == null);

        // open filter view via contextmenu
        this.rightClickOn("Proof Tree ");
        this.clickOn("Filter by text");

        // check if filter view is open
        assertTrue(((HBox) find("#filterViewHBox")).isVisible());

        // close filterView
        clickOn("X");

        // check if filter view is closed
        assertTrue((HBox) find("#filterViewHBox") == null);

        // open filter view via contextmenu
        this.rightClickOn("Proof Tree ");
        this.clickOn("Filter by text");

        // close filter view with ESC
        this.press(KeyCode.ESCAPE);

        // check if filter view is closed
        assertTrue((HBox) find("#filterViewHBox") == null);

        // open filter view via contextmenu
        this.rightClickOn("Proof Tree ");
        this.clickOn("Filter by text");

        // check if filter view is open again
        assertTrue(((HBox) find("#filterViewHBox")).isVisible());

        // filter
        enterFilterText("and");

        // disable filter
        clickOn("F");

        // enable filter
        clickOn("F");
    }

    /**
     * apply filter on tree
     * 
     * @param filterText
     */
    private void enterFilterText(final String filterText) {
        // select current filtertext to overwrite it
        this.push((KeyCodeCombination) KeyCombination.keyCombination("Ctrl+A"));

        this.write(filterText);
    }
}
