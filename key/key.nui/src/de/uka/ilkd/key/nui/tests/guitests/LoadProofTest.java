package de.uka.ilkd.key.nui.tests.guitests;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.ProgressIndicator;
import javafx.scene.input.KeyCode;

/**
 * Test for User Story. - #14664 Laden von Beweisen - #15076 Laden von
 * .key-Dateien
 * 
 * @author Florian Breitfelder
 *
 */

@SuppressWarnings("PMD.AtLeastOneConstructor")
// PMD will also complain if adding the constructor, then saying "avoid useless
// constructors"
public class LoadProofTest extends NUITestHelper {

    /**
     * Test for navigating through a proof tree.
     * 
     * @throws InterruptedException
     */
    @Test
    public void example01TestProof() {
        // test load proof
        loadProof("example01.proof", false);

        /*
         * navigate through example01 proof tree; root node should be opened
         */
        clickOn("0: andRight ");
        doubleClickOn("Case 1 ");
        clickOn("1: andRight ");
        doubleClickOn("Case 2 ");
        clickOn("4: equiv_right ");

        rightClickOn("Proof Tree ");
        clickOn("Collapse All");
    }

    /**
     * Test for navigating through a proof tree.
     */
    @Test
    public void example02TestProof() {
        // test load proof
        loadProof("example02.proof", false);

        /*
         * navigate through example01 proof tree; root node should be opened
         */
        clickOn("0: {} ");
        doubleClickOn("a TRUE ");
        clickOn("1: OPEN GOAL ");
        doubleClickOn("a FALSE ");
        clickOn("2: notRight ");
        clickOn("3: OPEN GOAL ");

        rightClickOn("Proof Tree ");
        clickOn("Collapse All");
    }

    /**
     * Test for loading a key file.
     */
    @Test
    public void example01TestKey() {
        // test load proof
        loadProof("example01.key", false);
    }

    /**
     * Test for canceling the loading process.
     */
    @Test
    public void testCancelLoadingProcess() {
        final String proofFile = "gcd.twoJoins.proof";
        // test load proof
        loadProof(proofFile, true);

        assertNull(dataModel.getTreeViewState(proofFile));
    }

    /**
     * Test for navigating through a proof tree.
     * 
     * @throws InterruptedException
     */
    @Test
    public void testFeedbackWhileLoading() {
        // test load proof
        String filename = "gcd.twoJoins.proof";

        // open load file dialog
        clickOn("File").clickOn("Open Proof...");

        // Enter file name: example01.proof
        final KeyCodeHelper key = new KeyCodeHelper(this);
        key.typeKeys(key.getKeyCode(filename.toUpperCase()));

        // press enter to load file
        type(KeyCode.ENTER);

        final Label label = ((Label) find("#statustext"));
        final ProgressIndicator progressIndicator = ((ProgressIndicator) find(
                "#progressIndicator"));
        final Button cancelButton = ((Button) find("#cancelButton"));

        String statusText = label.getText();
        boolean progressIndicatorVisible = progressIndicator.isVisible();
        boolean cancelButtonVisible = cancelButton.isVisible();

        while (!statusText.equals("Ready.")) {
            assertEquals("Loading file " + filename
                    + ", to stop loading click on cancel.", statusText);
            assertTrue(progressIndicatorVisible);
            assertTrue(cancelButtonVisible);

            statusText = label.getText();
            progressIndicatorVisible = progressIndicator.isVisible();
            cancelButtonVisible = cancelButton.isVisible();
        }
        sleep(500); // wait after changing statustext to Ready.
                    // to change progressIndicators and cancelButtons visibility
                    // to false
        assertEquals("Ready.", label.getText());
        assertFalse(progressIndicator.isVisible());
        assertFalse(cancelButton.isVisible());
    }

}
