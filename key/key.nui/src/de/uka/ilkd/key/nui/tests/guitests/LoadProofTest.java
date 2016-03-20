package de.uka.ilkd.key.nui.tests.guitests;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

/**
 * Test for User Story.
 * (010) Laden von Beweisen #14664.
 * 
 * Using: example01.proof; example02.proof
 * 
 * @author Florian Breitfelder
 *
 */
public class LoadProofTest extends NUITest {

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

        assertTrue(dataModel.getTreeViewState("proofFile") == null);
    }

}
