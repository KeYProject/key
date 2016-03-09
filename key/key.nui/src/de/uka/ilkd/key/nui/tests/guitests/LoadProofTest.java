package de.uka.ilkd.key.nui.tests.guitests;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import javafx.scene.control.Label;
import javafx.scene.control.ProgressIndicator;

/**
 * Test for User Story (010) Laden von Beweisen #14664
 * 
 * Using: example01.proof; example02.proof
 * 
 * @author Florian Breitfelder
 *
 */
public class LoadProofTest extends NUITest {

    @Test
    public void example01TestProof() throws InterruptedException {
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

    @Test
    public void example01TestKey() {
        // test load proof
        loadProof("example01.key", false);
    }

    @Test(timeout=30000)
    public void testCancelLoadingProcess() {
        // test load proof
        loadProof("gcd.twoJoins.proof", true);        
    }

}
