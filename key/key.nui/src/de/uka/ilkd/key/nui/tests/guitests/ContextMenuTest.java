package de.uka.ilkd.key.nui.tests.guitests;

import org.junit.Test;

public class ContextMenuTest extends NUITestHelper {

    @Test
    public void testContextMenuFilters() {
        // test load proof
        loadProof("example01.proof", false);

        // expand tree
        this.rightClickOn("Proof Tree ");
        this.clickOn("Expand All");

        // enable "Hide Closed" filter by contextmenu
        this.rightClickOn("Proof Tree ");
        this.clickOn("Hide Closed");

        // enable "Hide Non-Symbolic-Execution" filter by contextmenu
        this.rightClickOn("Proof Tree ");
        this.clickOn("Hide Non-Symbolic-Execution");

        // enable "Hide Non-Interactive" filter by contextmenu
        this.rightClickOn("Proof Tree ");
        this.clickOn("Hide Non-Interactive");

        // enable "Hide Intermediate" filter by contextmenu
        this.rightClickOn("Proof Tree ");
        this.clickOn("Hide Intermediate");
    }

    @Test
    public void testContextExpandCollapse() {
        // test load proof
        loadProof("example01.proof", false);

        // Expand Below
        this.rightClickOn("Proof Tree ");
        this.clickOn("Expand All");

        // Collapse Below
        this.rightClickOn("Proof Tree ");
        this.clickOn("Collapse All");

        // Expand Below
        this.rightClickOn("Proof Tree ");
        this.clickOn("Expand Below");

        // Collapse Below
        this.rightClickOn("Proof Tree ");
        this.clickOn("Collapse Below");

    }

}
