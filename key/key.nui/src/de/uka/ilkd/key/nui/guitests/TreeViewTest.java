package de.uka.ilkd.key.nui.guitests;

import java.io.File;

import org.junit.Test;
import org.loadui.testfx.GuiTest;

import de.uka.ilkd.key.nui.ComponentFactory;
import de.uka.ilkd.key.nui.controller.TreeViewController;
import de.uka.ilkd.key.nui.prooftree.ProofTreeStyle;
import javafx.geometry.VerticalDirection;
import javafx.scene.Parent;

/**
 * Test for User Stroy 2
 * 
 * Basic tests for treeView Component
 * 
 * @author Florian Breitfelder
 *
 */
public class TreeViewTest extends GuiTest {

    private Parent root = null;

    @Override
    public Parent getRootNode() {
    	// Retrieve component factory and create treeView
    	ComponentFactory factory = ComponentFactory.getInstance();
    	ComponentFactory.setResourceDirectory("components/");
    	root = factory.createComponent("treeView", "treeView.fxml");
    	
    	// Get controller and load default proof file
    	TreeViewController tvc = ComponentFactory.getInstance().getController("treeView");
    	tvc.loadAndDisplayProof(new File("resources//de/uka//ilkd//key//examples//example01.proof"));
    	
        return root;
    }

    @Test
    public void testTreeNavigation() {
    	doubleClickOn("." + ProofTreeStyle.CSS_NODE_BRANCH);
    	// TODO test is not working. Find a way to address nodes in the tree.
        for (int i = 0; i < 15; i++) {
        	doubleClickOn("#Proof_Tree");
        }

        for (int i = 0; i < 25; i++) {
            scroll(VerticalDirection.DOWN);
        }

        doubleClickOn("#if_x_true");
        doubleClickOn("#if_x_false");
    }
}
