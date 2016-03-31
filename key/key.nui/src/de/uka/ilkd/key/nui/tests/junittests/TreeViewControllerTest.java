package de.uka.ilkd.key.nui.tests.junittests;

import static org.junit.Assert.*;
import org.junit.Before;
import org.junit.Test;

import de.uka.ilkd.key.nui.DataModel;
import de.uka.ilkd.key.nui.IconFactory;
import de.uka.ilkd.key.nui.controller.FilterViewController;
import de.uka.ilkd.key.nui.controller.SearchViewController;
import de.uka.ilkd.key.nui.controller.TreeViewController;
import de.uka.ilkd.key.nui.prooftree.FilteringHandler;
import de.uka.ilkd.key.nui.prooftree.NUINode;
import javafx.application.Application;
import javafx.application.Platform;
import javafx.scene.control.TreeView;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Pane;
import javafx.scene.layout.VBox;
import javafx.stage.Stage;

public class TreeViewControllerTest extends Application {

    private TreeViewController treeViewController = new TreeViewController();

    @Before
    public void setUp() {
        treeViewController = new TreeViewController();
    }

    @Test
    public void testFilteringHandler() {
        FilteringHandler testvalue = new FilteringHandler(new DataModel(null, null));
        treeViewController.setFilteringHandler(testvalue);
        assertEquals(testvalue, treeViewController.getFilteringHandler());
    }

    @Test
    public void testFilterViewHBox() {
        HBox testvalue = new HBox();
        treeViewController.setFilterViewHBox(testvalue);
        assertEquals(testvalue, treeViewController.getFilterViewHBox());
    }

    @Test
    public void testFltrVwCtrlr() {
        FilterViewController testvalue = new FilterViewController();
        treeViewController.setFltrVwCtrlr(testvalue);
        assertEquals(testvalue, treeViewController.getFltrVwCtrlr());
    }

    @Test
    public void testIcf() {
        IconFactory testvalue = new IconFactory(0, 0);
        treeViewController.setIcf(testvalue);
        assertEquals(testvalue, treeViewController.getIcf());
    }

    @Test
    public void testProofTreeView() {
        Application.launch();
        TreeView<NUINode> testvalue = new TreeView<>();
        treeViewController.setProofTreeView(testvalue);
        assertEquals(testvalue, treeViewController.getProofTreeView());
    }

    @Test
    public void testSearchViewCtrlr() {
        SearchViewController testvalue = new SearchViewController();
        treeViewController.setSearchViewCtrlr(testvalue);
        assertEquals(testvalue, treeViewController.getSearchViewCtrlr());
    }

    @Test
    public void testSearchViewPane() {
        Pane testvalue = new Pane();
        treeViewController.setSearchViewPane(testvalue);
        assertEquals(testvalue, treeViewController.getSearchViewPane());
    }

    @Test
    public void testTreeViewPane() {
        VBox testvalue = new VBox();
        treeViewController.setTreeViewPane(testvalue);
        assertEquals(testvalue, treeViewController.getTreeViewPane());
    }

    @Override
    public void start(Stage primaryStage) {
        Platform.exit();
    }

}
