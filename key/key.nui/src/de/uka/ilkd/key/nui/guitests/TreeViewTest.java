package de.uka.ilkd.key.nui.guitests;

import org.junit.Test;
import org.loadui.testfx.GuiTest;

import de.uka.ilkd.key.nui.ComponentFactory;
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
        ComponentFactory factory = ComponentFactory.getInstance();
        root = factory.createComponent("treeView", "treeView");
        return root;
    }

    @Test
    public void testTreeNavigation() {
        doubleClickOn("#Proof_Tree");
        for (int i = 0; i < 15; i++) {
            doubleClickOn("#" + i);
        }

        for (int i = 0; i < 25; i++) {
            scroll(VerticalDirection.DOWN);
        }

        doubleClickOn("#if_x_true");
        doubleClickOn("#if_x_false");
    }
}
