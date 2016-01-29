package de.uka.ilkd.key.nui.tests.guitests;

import java.io.File;

import org.junit.Test;
import org.loadui.testfx.GuiTest;

import de.uka.ilkd.key.nui.ComponentFactory;
import de.uka.ilkd.key.nui.controller.TreeViewController;
import de.uka.ilkd.key.nui.prooftree.ProofTreeStyle;
import javafx.geometry.VerticalDirection;
import javafx.scene.Parent;
import javafx.scene.input.KeyCode;

/**
 * Test for User Stroys
 * (002) Beweisbaumvisualisierung #14298
 * (007) Farbige Hinterlegung von Knoten im Beweisbaum #14662
 * (008) Icons im Beweisbaum #14470
 * (009) Basis Kontextmenu mit "Expand/Collapse all" #14663
 * 
 * Basic tests for treeView Component
 * 
 * @author Florian Breitfelder
 *
 */
public class TreeViewTest extends GuiTest {

    private Parent root = null;

    @Override
    /*public Parent getRootNode() {
    	// Retrieve component factory and create treeView
    	ComponentFactory factory = ComponentFactory.getInstance();
    	ComponentFactory.setResourceDirectory("components/");
    	root = factory.createComponent("treeView", "treeView.fxml");
    	
    	// Get controller and load default proof file
    	TreeViewController tvc = ComponentFactory.getInstance().getController("treeView");
    	tvc.loadAndDisplayProof(new File("resources//de/uka//ilkd//key//examples//example01.proof"));
    	
        return root;
    }*/

    
    public Parent getRootNode() {
        ComponentFactory factory = ComponentFactory.getInstance();
        ComponentFactory.setResourceDirectory("components/");
        root = factory.createNUISceneGraph();
        return root;
    }

    @Test
    public void testTreeNavigation() {
        // open load file dialog
        clickOn("File").clickOn("Open Proof...");

        // Enter file name: example01.proof
        type(KeyCode.E).type(KeyCode.X).type(KeyCode.A).type(KeyCode.M)
                .type(KeyCode.P).type(KeyCode.L).type(KeyCode.E)
                .type(KeyCode.DIGIT0).type(KeyCode.DIGIT1).type(KeyCode.PERIOD)
                .type(KeyCode.P).type(KeyCode.R).type(KeyCode.O).type(KeyCode.O)
                .type(KeyCode.F);

        // press enter to load file
        type(KeyCode.ENTER);
        
    	doubleClickOn("." + ProofTreeStyle.CSS_NODE_BRANCH);
    	clickOn("0: andRight ");
    	doubleClickOn("Case 1 ");
    	doubleClickOn("Case 2 ");
    	doubleClickOn("Case 1 ");
    	rightClickOn().clickOn("Expand All");
    	clickOn("Case 1");
    	rightClickOn().clickOn("Expand All");
    	clickOn("Case 1");
    	rightClickOn().clickOn("Expand All");
    	clickOn("Case 1");
    	rightClickOn().clickOn("Expand All");
    	clickOn("Case 1");
    	rightClickOn().clickOn("Expand All");
    	clickOn("Case 1");
    	//rightClickOn().clickOn("Expand Below");
    	//rightClickOn().clickOn("Collapse All");
    	//rightClickOn().clickOn("Collapse Below");
    	/*rightClickOn().clickOn("Search");
    	rightClickOn().clickOn("Search");
    	rightClickOn().clickOn("Search");
    	rightClickOn().clickOn("Search");
    	rightClickOn().clickOn("Search");
    	rightClickOn().clickOn("Search");
    	rightClickOn().clickOn("Search");
    	rightClickOn().clickOn("Search");
    	rightClickOn().clickOn("Search");
    	rightClickOn().clickOn("Search");
    	rightClickOn().clickOn("Search");
    	
    	write("Case 1");*/
    	// TODO test is not working. Find a way to address nodes in the tree.
       /* for (int i = 0; i < 15; i++) {
        	doubleClickOn("#Proof_Tree");
        }

        for (int i = 0; i < 25; i++) {
            scroll(VerticalDirection.DOWN);
        }

        doubleClickOn("#if_x_true");
        doubleClickOn("#if_x_false");*/
    }
}
