package de.uka.ilkd.key.nui.tests.guitests;

import org.junit.Test;

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
    public void example01Test() throws InterruptedException {
        // test load proof
        loadProof("example01.proof");

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
    public void example02Test() {
        // test load proof
        loadProof("example02.proof");

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

}
