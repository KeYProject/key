package de.uka.ilkd.key.nui.tests.guitests;

import org.loadui.testfx.GuiTest;

import de.uka.ilkd.key.nui.ComponentFactory;
import javafx.scene.Parent;

/**
 * Test for User Stroy (005) Suchen im Beweisbaum #14469
 * 
 * Basic tests for treeView Component
 * 
 * @author Florian Breitfelder
 *
 */
public class SearchViewTest extends GuiTest {

    // the root of the scene graph
    private Parent root = null;

    @Override
    public Parent getRootNode() {
        ComponentFactory factory = ComponentFactory.getInstance();
        ComponentFactory.setResourceDirectory("components/");
        root = factory.createNUISceneGraph();
        return root;
    }

}
