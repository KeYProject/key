package de.uka.ilkd.key.nui.tests.guitests;

import static org.junit.Assert.*;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;

import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;

public class AddNewFilterTest extends NUITest {
    private static File filterS = new File(
            "bin//de/uka//ilkd//key//nui//tests//guitests//TestFilter.class");
    private static File filterD = new File(
            "bin//de/uka//ilkd//key//nui//prooftree//filter//TestFilter.class");

    @BeforeClass
    public static void initTest() throws IOException {
        com.google.common.io.Files.copy(filterS, filterD);
    }

    @AfterClass
    public static void finishing() throws IOException {
        Files.delete(filterD.toPath());
    }

    /**
     * checks if new filter was loaded
     */
    @Test
    public void testAddingNewFilter() {
        // test load proof
        loadProof("example01.proof", false);

        // expand tree
        this.rightClickOn("Proof Tree ");
        this.clickOn("Expand All");

        // check if filter is disabled
        assertTrue(dataModel.getLoaddTriVwStat().getTreeItem()
                .getFilteredChildren().size() > 0);

        // open filter view via contextmenu
        this.rightClickOn("Proof Tree ");
        this.clickOn("TestFilter");

        // check if filter is enabled
        assertEquals(0, dataModel.getLoaddTriVwStat().getTreeItem()
                .getFilteredChildren().size());
    }

}
