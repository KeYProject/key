package de.uka.ilkd.key.nui.tests.guitests;

import static org.junit.Assert.*;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.Arrays;

import javax.tools.JavaCompiler;
import javax.tools.JavaFileObject;
import javax.tools.StandardJavaFileManager;
import javax.tools.ToolProvider;

import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;

public class AddNewFilterTest extends NUITestHelper {

    // Source file
    private static String filterS = "bin//de/uka//ilkd//key//nui//tests//guitests//TestFilter";
    private static File filterS_class = new File(filterS + ".class");
    private static File filterS_java = new File(filterS + ".java");

    // Destination file
    private static File filterD = new File(
            "bin//de/uka//ilkd//key//nui//prooftree//filter//TestFilter.class");

    @BeforeClass
    public static void initTest() throws IOException {
        // Compile the .java filter file
        JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
        StandardJavaFileManager fileManager = compiler
                .getStandardFileManager(null, null, null);
        Iterable<? extends JavaFileObject> compilationUnits1 = fileManager
                .getJavaFileObjectsFromFiles(Arrays.asList(filterS_java));
        compiler.getTask(null, fileManager, null, null, null, compilationUnits1)
                .call();

        // Copy compiled file (.class) into the filter package
        com.google.common.io.Files.copy(filterS_class, filterD);
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
