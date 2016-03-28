package de.uka.ilkd.key.nui.tests.guitests;

import static org.junit.Assert.*;

import org.junit.Test;

import de.uka.ilkd.key.nui.TreeViewState;
import de.uka.ilkd.key.nui.prooftree.ProofTreeItem;
import javafx.scene.Node;
import javafx.scene.input.KeyCode;

/**
 * Test for User Stroys. 
 * - #14298 Beweisbaumvisualisierung 
 * - #14299 Einrückung linearer Beweisbaumabschnitte
 * - #15078 Automatisches Aufklappen der Wurzel im Beweisbaum
 * 
 * @author Florian Breitfelder
 *
 */

@SuppressWarnings("PMD.AtLeastOneConstructor")
//PMD will also complain if adding the constructor, then saying "avoid useless constructors"
public class TreeViewTest extends NUITest {

    @Test
    public void testTreeOne() {
        // open load file dialog
        clickOn("File").clickOn("Open Proof...");

        // Enter file name: example01.proof
        final KeyCodeHelper key = new KeyCodeHelper(this);
        key.typeKeys(key.getKeyCode("EXAMPLE01.PROOF"));

        // press enter to load file
        type(KeyCode.ENTER);

        waitUntilStatusIs("Ready.");

        clickOn("0: andRight ");
        doubleClickOn("Case 1 ");
        doubleClickOn("Case 2 ");
        doubleClickOn("Case 1 ");
        rightClickOn().clickOn("Expand All");

        // take screenshot
        captureScreenshot();
    }

    @Test
    public void testTreeTwo() {
        // open load file dialog
        clickOn("File").clickOn("Open Proof...");

        // Enter file name: example02.proof
        final KeyCodeHelper key = new KeyCodeHelper(this);
        key.typeKeys(key.getKeyCode("EXAMPLE02.PROOF"));

        // press enter to load file
        type(KeyCode.ENTER);

        waitUntilStatusIs("Ready.");

        // Expand All
        clickOn("Proof Tree ");
        rightClickOn().clickOn("Expand All");

        // Load model
        TreeViewState treeViewState = dataModel.getLoaddTriVwStat();
        ProofTreeItem rootProofTreeItem = treeViewState.getTreeItem();

        // walk through the tree
        treeDown(rootProofTreeItem);

        // take screenshot
        captureScreenshot();
    }

    @Test
    public void testTreeThree() {
        // open load file dialog
        clickOn("File").clickOn("Open Proof...");

        // Enter file name: gcd.twoJoins.proof
        final KeyCodeHelper key = new KeyCodeHelper(this);
        key.typeKeys(key.getKeyCode("GCD.TWOJOINS.PROOF"));

        // press enter to load file
        type(KeyCode.ENTER);

        waitUntilStatusIs("Ready.");

        // Expand All
        clickOn("Proof Tree ");
        rightClickOn().clickOn("Expand All");

        // take screenshot
        captureScreenshot();
    }

    /**
     * Used to walk through the tree recursively. Only for testTreeTwo
     * 
     * @param proofTreeItem
     */
    private void treeDown(ProofTreeItem proofTreeItem) {
        for (int i = 0; i < proofTreeItem.getInternalChildren().size(); i++) {
            Node node = find(
                    proofTreeItem.getChildren().get(i).getValue().toString()
                            + " ");
            if (node != null) {
                clickOn(node);
            }
            treeDown(proofTreeItem.getInternalChildren().get(i));
        }
    }

    @Test
    public void testRootExpandedOne() {
        // open load file dialog
        clickOn("File").clickOn("Open Proof...");

        // Enter file name: example01.proof
        final KeyCodeHelper key = new KeyCodeHelper(this);
        key.typeKeys(key.getKeyCode("EXAMPLE01.PROOF"));

        // press enter to load file
        type(KeyCode.ENTER);

        waitUntilStatusIs("Ready.");

        // Load model
        TreeViewState treeViewState = dataModel.getLoaddTriVwStat();
        ProofTreeItem rootProofTreeItem = treeViewState.getTreeItem();

        assertTrue(rootProofTreeItem.isExpanded());

        // collapse root by double click
        doubleClickOn("Proof Tree ");

        assertFalse(rootProofTreeItem.isExpanded());
    }

    @Test
    public void testRootExpandedTwo() {
        // open load file dialog
        clickOn("File").clickOn("Open Proof...");

        // Enter file name: example02.proof
        final KeyCodeHelper key = new KeyCodeHelper(this);
        key.typeKeys(key.getKeyCode("EXAMPLE02.PROOF"));

        // press enter to load file
        type(KeyCode.ENTER);

        waitUntilStatusIs("Ready.");

        // Load model
        TreeViewState treeViewState = dataModel.getLoaddTriVwStat();
        ProofTreeItem rootProofTreeItem = treeViewState.getTreeItem();

        assertTrue(rootProofTreeItem.isExpanded());

        // collapse root by double click
        doubleClickOn("Proof Tree ");

        assertFalse(rootProofTreeItem.isExpanded());
    }

    @Test
    public void testRootExpandedThree() {
        // open load file dialog
        clickOn("File").clickOn("Open Proof...");

        // Enter file name: gcd.twoJoins.proof
        final KeyCodeHelper key = new KeyCodeHelper(this);
        key.typeKeys(key.getKeyCode("GCD.TWOJOINS.PROOF"));

        // press enter to load file
        type(KeyCode.ENTER);

        waitUntilStatusIs("Ready.");

        // Load model
        TreeViewState treeViewState = dataModel.getLoaddTriVwStat();
        ProofTreeItem rootProofTreeItem = treeViewState.getTreeItem();

        assertTrue(rootProofTreeItem.isExpanded());

        // collapse root by double click
        doubleClickOn("Proof Tree ");

        assertFalse(rootProofTreeItem.isExpanded());
    }
}
